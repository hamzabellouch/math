import OAI.Probability.LatticePassage.Stationarity
import OAI.Probability.LatticePassage.LocalPassage

namespace OAI

namespace CompanionFPP
open MeasureTheory

noncomputable instance encodable_lattice_walk (x y : Vertex) : Encodable (lattice.Walk x y) :=
  Encodable.ofCountable _

noncomputable def enumerateWalk (x y : Vertex) (n : ℕ) : lattice.Walk x y :=
  (Encodable.decode (α := lattice.Walk x y) n).getD (Classical.choice (lattice_walk x y))

lemma enumerateWalk_surjective (x y : Vertex) : Function.Surjective (enumerateWalk x y) := by
  intro p
  exact ⟨Encodable.encode p, by simp [enumerateWalk]⟩

def minimizesLocally (x y : Vertex) (R n : ℕ) (ω : Environment) : Prop :=
  (enumerateWalk x y n).IsPath ∧ (enumerateWalk x y n).length < R ∧
    pathCost ω (enumerateWalk x y n) = localPassageTime ω x y R

lemma exists_minimizesLocally (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (ω : Environment) : ∃ n, minimizesLocally x y R n ω := by
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  obtain ⟨n,rfl⟩ := enumerateWalk_surjective x y p
  exact ⟨n,hp,hl,hm⟩

lemma measurableSet_minimizesLocally (x y : Vertex) (R n : ℕ) :
    MeasurableSet {ω : Environment | minimizesLocally x y R n ω} := by
  unfold minimizesLocally
  by_cases hp : (enumerateWalk x y n).IsPath
  · by_cases hl : (enumerateWalk x y n).length < R
    · simpa [hp,hl] using measurableSet_eq_fun (measurable_pathCost (enumerateWalk x y n))
        (measurable_localPassageTime x y R)
    · simp [hl]
  · simp [hp]

noncomputable def localSelectionIndex (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (ω : Environment) : ℕ := by
  classical
  exact Nat.find (exists_minimizesLocally x y R hR ω)

@[fun_prop] theorem measurable_localSelectionIndex (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) : Measurable (localSelectionIndex x y R hR) := by
  classical
  exact measurable_find _ (measurableSet_minimizesLocally x y R)

noncomputable def selectedLocalPath (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (ω : Environment) : lattice.Walk x y :=
  enumerateWalk x y (localSelectionIndex x y R hR ω)

theorem selectedLocalPath_spec (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (ω : Environment) :
    (selectedLocalPath x y R hR ω).IsPath ∧
    (selectedLocalPath x y R hR ω).length < R ∧
    pathCost ω (selectedLocalPath x y R hR ω) = localPassageTime ω x y R := by
  classical
  exact Nat.find_spec (exists_minimizesLocally x y R hR ω)

theorem measurable_selectedLocalPath_observation (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (f : lattice.Walk x y → ℝ) :
    Measurable (fun ω => f (selectedLocalPath x y R hR ω)) := by
  exact (measurable_of_countable (f := fun n : ℕ => f (enumerateWalk x y n))).comp
    (measurable_localSelectionIndex x y R hR)

theorem selectedLocalPath_eq_of_agree (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (ω ω' : Environment)
    (h : ∀ e ∈ localEdges x R, ω e = ω' e) :
    selectedLocalPath x y R hR ω = selectedLocalPath x y R hR ω' := by
  classical
  have he : ∀ n, minimizesLocally x y R n ω ↔ minimizesLocally x y R n ω' := by
    intro n
    unfold minimizesLocally
    by_cases hp : (enumerateWalk x y n).IsPath
    · by_cases hl : (enumerateWalk x y n).length < R
      · rw [local_pathCost_eq ω ω' h _ hp hl,
          localPassageTime_eq_of_agree ω ω' x y R h]
      · simp [hl]
    · simp [hp]
  unfold selectedLocalPath localSelectionIndex
  congr 1
  exact Nat.find_congr' (fun {n} => he n)

end CompanionFPP

end OAI

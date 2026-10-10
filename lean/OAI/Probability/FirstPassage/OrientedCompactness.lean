import OAI.Probability.FirstPassage.ProbabilityFoundations
import Mathlib.Data.Finset.Union

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory

def orientedSurvival (G : Vertex → Prop) (p : Vertex) : ℕ → Prop
  | 0 => True
  | n+1 => G p ∧ (orientedSurvival G (p+(1,0)) n ∨ orientedSurvival G (p+(0,1)) n)

def infiniteOrientedPath (G : Vertex → Prop) (p : Vertex) : Prop :=
  ∃ z : ℕ → Vertex, z 0=p ∧
    (∀ n, z (n+1)=z n+(1,0) ∨ z (n+1)=z n+(0,1)) ∧ ∀ n, G (z n)

theorem orientedSurvival_pred (G : Vertex → Prop) (p : Vertex) (n : ℕ)
    (h : orientedSurvival G p (n+1)) : orientedSurvival G p n := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    refine ⟨h.1,?_⟩
    rcases h.2 with he | hn
    · exact Or.inl (ih _ he)
    · exact Or.inr (ih _ hn)

theorem orientedSurvival_mono (G : Vertex → Prop) (p : Vertex) {m n : ℕ}
    (hmn : m ≤ n) (h : orientedSurvival G p n) : orientedSurvival G p m := by
  induction n,hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih => exact ih (orientedSurvival_pred G p n h)

theorem oriented_surviving_successor (G : Vertex → Prop) (p : Vertex)
    (h : ∀ n, orientedSurvival G p n) :
    (∀ n, orientedSurvival G (p+(1,0)) n) ∨ (∀ n, orientedSurvival G (p+(0,1)) n) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨m,hm⟩,⟨n,hn⟩⟩ := hn
  rcases (h (max m n+1)).2 with he | he
  · exact hm (orientedSurvival_mono G _ (le_max_left _ _) he)
  · exact hn (orientedSurvival_mono G _ (le_max_right _ _) he)

theorem infiniteOrientedPath_iff (G : Vertex → Prop) (p : Vertex) :
    infiniteOrientedPath G p ↔ ∀ n, orientedSurvival G p n := by
  classical
  constructor
  · rintro ⟨z,hz,hstep,hG⟩
    have hh (n m : ℕ) : orientedSurvival G (z m) n := by
      induction n generalizing m with
      | zero => trivial
      | succ n ih =>
        refine ⟨hG m,?_⟩
        have ht := ih (m+1)
        rcases hstep m with he | he
        · exact Or.inl (he ▸ ht)
        · exact Or.inr (he ▸ ht)
    intro n
    simpa [hz] using hh n 0
  · intro h
    let V := {q : Vertex // ∀ n, orientedSurvival G q n}
    have next (q : V) : ∃ r : V, r.val=q.val+(1,0) ∨ r.val=q.val+(0,1) := by
      rcases oriented_surviving_successor G q.val q.property with he | hn
      · exact ⟨⟨q.val+(1,0),he⟩,Or.inl rfl⟩
      · exact ⟨⟨q.val+(0,1),hn⟩,Or.inr rfl⟩
    let step (q : V) : V := (next q).choose
    let z : ℕ → V := Nat.rec ⟨p,h⟩ (fun _ q => step q)
    refine ⟨fun n => (z n).val,rfl,?_,?_⟩
    · intro n
      exact (next (z n)).choose_spec
    · intro n
      exact ((z n).property 1).1

noncomputable def orientedEndpoints (G : Vertex → Prop) (p : Vertex) : ℕ → Finset Vertex := by
  classical
  exact fun n => match n with
  | 0 => {p}
  | n+1 => if G p then orientedEndpoints G (p+(1,0)) n ∪ orientedEndpoints G (p+(0,1)) n else ∅

theorem orientedEndpoints_nonempty_iff (G : Vertex → Prop) (p : Vertex) (n : ℕ) :
    (orientedEndpoints G p n).Nonempty ↔ orientedSurvival G p n := by
  classical
  induction n generalizing p with
  | zero => simp [orientedEndpoints,orientedSurvival]
  | succ n ih =>
    by_cases hg : G p <;> simp [orientedEndpoints,orientedSurvival,hg,Finset.union_nonempty,ih]

def orientedReachable (G : Vertex → Prop) (p : Vertex) : Set Vertex :=
  ⋃ n : ℕ, (orientedEndpoints G p n : Set Vertex)

theorem orientedReachable_finite_of_no_infinite_path (G : Vertex → Prop) (p : Vertex)
    (h : ¬infiniteOrientedPath G p) : (orientedReachable G p).Finite := by
  classical
  rw [infiniteOrientedPath_iff] at h
  push Not at h
  obtain ⟨N,hN⟩ := h
  have hs : orientedReachable G p ⊆ ((Finset.range N).biUnion (orientedEndpoints G p) : Set Vertex) := by
    intro q hq
    obtain ⟨n,hn⟩ := mem_iUnion.mp hq
    have hsurv := (orientedEndpoints_nonempty_iff G p n).mp ⟨q,hn⟩
    have hnN : n < N := by
      by_contra hnN
      exact hN (orientedSurvival_mono G p (by omega) hsurv)
    exact mem_biUnion.mpr ⟨n,mem_range.mpr hnN,hn⟩
  exact (Finset.finite_toSet _).subset hs

theorem orientedReachable_origin (G : Vertex → Prop) (p : Vertex) : p ∈ orientedReachable G p := by
  exact mem_iUnion.mpr ⟨0,by simp [orientedEndpoints]⟩

theorem orientedEndpoints_extend (G : Vertex → Prop) (p q : Vertex) (n : ℕ)
    (hq : q ∈ orientedEndpoints G p n) (hg : G q) :
    q+(1,0) ∈ orientedEndpoints G p (n+1) ∧ q+(0,1) ∈ orientedEndpoints G p (n+1) := by
  classical
  induction n generalizing p with
  | zero =>
    have he : q=p := by simpa [orientedEndpoints] using hq
    subst q
    simp [orientedEndpoints,hg]
  | succ n ih =>
    by_cases hp : G p
    · simp only [orientedEndpoints,ite_eq_left hp,Finset.mem_union] at hq ⊢
      rcases hq with he | hn
      · obtain ⟨h1,h2⟩ := ih _ he
        exact ⟨Or.inl h1,Or.inl h2⟩
      · obtain ⟨h1,h2⟩ := ih _ hn
        exact ⟨Or.inr h1,Or.inr h2⟩
    · simp [orientedEndpoints,hp] at hq

theorem orientedReachable_forward (G : Vertex → Prop) (p q : Vertex)
    (hq : q ∈ orientedReachable G p) (hg : G q) :
    q+(1,0) ∈ orientedReachable G p ∧ q+(0,1) ∈ orientedReachable G p := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp hq
  obtain ⟨h1,h2⟩ := orientedEndpoints_extend G p q n hn hg
  exact ⟨mem_iUnion.mpr ⟨n+1,h1⟩,mem_iUnion.mpr ⟨n+1,h2⟩⟩

theorem orientedReachable_boundary_bad (G : Vertex → Prop) (p q : Vertex)
    (hq : q ∈ orientedReachable G p)
    (hout : q+(1,0) ∉ orientedReachable G p ∨ q+(0,1) ∉ orientedReachable G p) : ¬G q := by
  intro hg
  have hh := orientedReachable_forward G p q hq hg
  exact hout.elim (fun h => h hh.1) (fun h => h hh.2)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_orientedSurvival (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) (n : ℕ) : MeasurableSet {ω | orientedSurvival (fun v => ω ∈ G v) p n} := by
  induction n generalizing p with
  | zero => simp [orientedSurvival]
  | succ n ih =>
    exact (hG p).inter ((ih (p+(1,0))).union (ih (p+(0,1))))

theorem measurableSet_infiniteOrientedPath (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) : MeasurableSet {ω | infiniteOrientedPath (fun v => ω ∈ G v) p} := by
  simp only [infiniteOrientedPath_iff,ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_orientedSurvival G hG p n)

end PlanarFPP

end OAI

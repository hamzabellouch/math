import Mathlib
import OAI.Analysis.HardSphere.FormDomain.HilbertJet
import OAI.Analysis.HardSphere.Geometry.LiftedBadComponent

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma microCube_cover (L : Length) {h : ℝ} (hh : 0 < h) (x : Torus L) :
    ∃ z, x ∈ microCube L h z := by
  let y : Point := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  let z : Vertex := fun j ↦ ⌊(y j + 1/2) / h⌋
  refine ⟨z, y, ⟨?_, ?_⟩, ?_⟩
  · intro j
    have hj := (le_div_iff₀ hh).mp (Int.floor_le ((y j + 1/2) / h))
    change h * (z j : ℝ) - 1/2 ≤ y j
    dsimp [z]
    nlinarith
  · intro j
    have hj := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((y j + 1/2) / h))
    change y j ≤ h * ((z j : ℝ) + 1) - 1/2
    dsimp [z]
    nlinarith
  · ext j
    exact AddCircle.coe_equivIco

lemma lower_corner_mem {h : ℝ} (hh : 0 ≤ h) (z : Vertex) :
    (fun j ↦ h * (z j : ℝ) - 1/2) ∈ liftedCube h z := by
  refine ⟨le_rfl, ?_⟩
  intro j
  dsimp
  nlinarith

lemma step_corner_mem {h : ℝ} (hh : 0 ≤ h) (z : Vertex) (i : Fin 3) :
    (fun j ↦ h * (step z i j : ℝ) - 1/2) ∈ liftedCube h z := by
  constructor <;> intro j <;> dsimp only
  · by_cases hj : j = i
    · subst j
      rw [step_apply_same, Int.cast_add, Int.cast_one]
      nlinarith
    · rw [step_apply_ne z hj]
  · by_cases hj : j = i
    · subst j
      rw [step_apply_same, Int.cast_add, Int.cast_one]
    · rw [step_apply_ne z hj]
      nlinarith

lemma adjacent_microCubes_inter (L : Length) {h : ℝ} (hh : 0 ≤ h)
    {z w : Vertex} (hzw : nearestStep z w) :
    (microCube L h z ∩ microCube L h w).Nonempty := by
  have hf (v : Vertex) (i : Fin 3) :
      (microCube L h v ∩ microCube L h (step v i)).Nonempty := by
    let y : Point := fun j ↦ h * (step v i j : ℝ) - 1/2
    exact ⟨liftPoint L y, ⟨y, step_corner_mem hh v i, rfl⟩,
      ⟨y, lower_corner_mem hh (step v i), rfl⟩⟩
  obtain ⟨i, rfl | rfl⟩ := nearestStep_eq_step hzw
  · exact hf z i
  · simpa only [Set.inter_comm] using hf w i

lemma exterior_all_liftedBadComponents_good (B : Set Vertex) (hfin : FiniteBadComponents B)
    {z : Vertex} (hz : ∀ C, IsBadComponent B C → z ∈ exterior C) : z ∉ B := by
  intro hzB
  let C := (hfin z hzB).toFinset
  have hC : IsBadComponent B C := ⟨z, hzB, (hfin z hzB).coe_toFinset⟩
  exact (hz C hC).1 ((hfin z hzB).mem_toFinset.mpr (liftedBadComponent_self hzB))

lemma goodCubes_reach_joined {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} (hh : 0 ≤ h) {z w : Vertex}
    (hz : z ∉ bad h r Y) (hzw : withinReach nearestStep (bad h r Y)ᶜ z w)
    {x y : Torus L} (hx : x ∈ microCube L h z) (hy : y ∈ microCube L h w) :
    JoinedIn (slice r Y) x y := by
  induction hzw generalizing y with
  | refl =>
    exact ((microCube_pathConnected L hh z).joinedIn x hx y hy).mono
      (goodCube_subset_slice hz)
  | @tail w u hzw hwu ih =>
    obtain ⟨p, hpw, hpu⟩ := adjacent_microCubes_inter L hh hwu.2.2
    exact (ih hpw).trans (((microCube_pathConnected L hh u).joinedIn p hpu y hy).mono
      (goodCube_subset_slice hwu.2.1))

theorem retained_joined {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} (hh : 0 < h) {x y : Torus L}
    (hx : x ∈ retained h r Y) (hy : y ∈ retained h r Y) :
    JoinedIn (slice r Y) x y := by
  obtain ⟨z, hxz⟩ := microCube_cover L hh x
  obtain ⟨w, hyw⟩ := microCube_cover L hh y
  have hf := retained_finiteComponents hx
  have hz := retained_mem_exterior hx hxz
  have hw := retained_mem_exterior hy hyw
  exact goodCubes_reach_joined hh.le
    (exterior_all_liftedBadComponents_good _ hf hz)
    (exterior_all_liftedBadComponents_reach _ hf hz hw) hxz hyw

end HardSphere.BathSlice

namespace HardSphere

end HardSphere

namespace HardSphere.BathSlice
open HardSphere.Lattice

attribute [local irreducible] torusDistance

theorem retained_strict_clearance {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} (hh : 0 < h) {x y : Torus L}
    (hx : x ∈ retained h r Y) (hy : y ∈ retained h r Y) :
    ∃ γ : Path x y, ∃ δ : ℝ, 0 < δ ∧
      ∀ (t : unitInterval) (j : Fin n), r + δ ≤ torusDistance L (γ t) (Y j) := by
  classical
  obtain ⟨γ, hγ⟩ := retained_joined hh hx hy
  cases isEmpty_or_nonempty (Fin n) with
  | inl he =>
    let := he
    exact ⟨γ, 1, by norm_num, fun _ j ↦ isEmptyElim j⟩
  | inr hn =>
    let := hn
    let f : unitInterval × Fin n → ℝ := fun p ↦ torusDistance L (γ p.1) (Y p.2) - r
    have hf : Continuous f := by
      apply Continuous.sub _ continuous_const
      exact (continuous_torusDistance L).comp
        ((γ.continuous.comp continuous_fst).prodMk
          ((continuous_of_discreteTopology : Continuous Y).comp continuous_snd))
    obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
    have hpos : 0 < f p := by
      have hd : r < torusDistance L (γ p.1) (Y p.2) := by
        apply lt_of_not_ge
        intro he
        exact hγ p.1 ⟨p.2, he⟩
      exact sub_pos.mpr hd
    refine ⟨γ, f p, hpos, ?_⟩
    intro t j
    have hm := hp (Set.mem_univ (t, j))
    dsimp [f] at hm ⊢
    linarith

lemma isClosed_bad_test {n : ℕ} (L : Length) (h r : ℝ) (z : Vertex) :
    IsClosed {Y : Configuration n L | z ∈ bad h r Y} := by
  let A : Set (Torus L × Configuration n L) :=
    {p | p.1 ∈ microCube L h z ∧ ∃ j, torusDistance L p.1 (p.2 j) ≤ r}
  have hA : IsClosed A := by
    apply IsClosed.inter ((isCompact_microCube L h z).isClosed.preimage continuous_fst)
    have he : {p : Torus L × Configuration n L | ∃ j, torusDistance L p.1 (p.2 j) ≤ r} =
        ⋃ j : Fin n, {p | torusDistance L p.1 (p.2 j) ≤ r} := by ext p; simp
    change IsClosed {p : Torus L × Configuration n L | ∃ j, torusDistance L p.1 (p.2 j) ≤ r}
    rw [he]
    apply isClosed_iUnion_of_finite
    intro j
    exact isClosed_le ((continuous_torusDistance L).comp
      (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))) continuous_const
  have he : {Y : Configuration n L | z ∈ bad h r Y} = Prod.snd '' A := by
    ext Y
    constructor
    · rintro ⟨x, hx, hxf⟩
      exact ⟨(x, Y), ⟨hx, hxf⟩, rfl⟩
    · rintro ⟨⟨x, Z⟩, hZ, he⟩
      cases he
      exact ⟨x, hZ⟩
  rw [he]
  exact isClosedMap_snd_of_compactSpace A hA

lemma measurableSet_bad_test {n : ℕ} (L : Length) (h r : ℝ) (z : Vertex) :
    MeasurableSet {Y : Configuration n L | z ∈ bad h r Y} :=
  (isClosed_bad_test L h r z).measurableSet

end HardSphere.BathSlice

end

end OAI

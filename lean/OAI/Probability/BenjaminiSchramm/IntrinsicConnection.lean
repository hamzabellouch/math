import OAI.Probability.BenjaminiSchramm.BallSnapshot

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def longConnectionEvent (G : BondGraph V E) (x y : V) (n : ℕ) : Set (Set E) :=
  {ω | Conn G ω x y ∧ n ≤ (openSimpleGraph G ω).dist x y}

def intrinsicSphereEvent (G : BondGraph V E) (x z : V) (j : ℕ) : Set (Set E) :=
  {ω | z ∈ intrinsicSphere G ω x j}

theorem measurableSet_intrinsicSphereEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (j : ℕ) (hj : 0 < j) : MeasurableSet (intrinsicSphereEvent G x z j) := by
  have he : intrinsicSphereEvent G x z j =
      {ω | z ∈ intrinsicBall G ω x j} \ {ω | z ∈ intrinsicBall G ω x (j-1)} := by
    ext ω
    exact Set.ext_iff.mp (intrinsicSphere_eq_ball_sdiff G ω x j hj) z
  rw [he]
  exact (measurableSet_mem_intrinsicBall G hloc x z j).diff
    (measurableSet_mem_intrinsicBall G hloc x z (j-1))

def snapshotFrontierCell (G : BondGraph V E) (x z : V) (j : ℕ)
    (a : Finset V × Finset V) : Set (Set E) :=
  if z ∈ a.2 \ a.1 then ballSnapshotCell G x j a.1 a.2 else ∅

theorem snapshotFrontierCell_iUnion (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (j : ℕ) (hj : 0 < j) :
    (⋃ a : Finset V × Finset V, snapshotFrontierCell G x z j a) = intrinsicSphereEvent G x z j := by
  ext ω
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    by_cases hz : z ∈ a.2 \ a.1
    · rw [snapshotFrontierCell,ite_eq_left hz] at ha
      change z ∈ intrinsicSphere G ω x j
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2]
      exact_mod_cast hz
    · simp only [snapshotFrontierCell,ite_eq_right hz,Set.mem_empty_iff_false] at ha
  · intro hz
    obtain ⟨a,ha⟩ := exists_ballSnapshotCell G hloc ω x j
    have hz' : z ∈ a.2 \ a.1 := by
      change z ∈ intrinsicSphere G ω x j at hz
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2] at hz
      exact_mod_cast hz
    exact Set.mem_iUnion.mpr ⟨a,by simpa only [snapshotFrontierCell,ite_eq_left hz'] using ha⟩

theorem snapshotFrontierCell_pairwise (G : BondGraph V E) (x z : V) (j : ℕ) :
    Pairwise (fun a b : Finset V × Finset V =>
      Disjoint (snapshotFrontierCell G x z j a) (snapshotFrontierCell G x z j b)) := by
  intro a b hab
  have ha : snapshotFrontierCell G x z j a ⊆ ballSnapshotCell G x j a.1 a.2 := by
    unfold snapshotFrontierCell; split <;> simp
  have hb : snapshotFrontierCell G x z j b ⊆ ballSnapshotCell G x j b.1 b.2 := by
    unfold snapshotFrontierCell; split <;> simp
  exact (ballSnapshotCell_pairwise G x j hab).mono ha hb

theorem measurableSet_snapshotFrontierCell [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x z : V) (j : ℕ) (a : Finset V × Finset V) :
    MeasurableSet (snapshotFrontierCell G x z j a) := by
  unfold snapshotFrontierCell
  split
  · exact measurableSet_ballSnapshotCell G hloc x j a.1 a.2
  · exact MeasurableSet.empty

theorem longConnection_sphere_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y : V) (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    law p (longConnectionEvent G x y n) ≤
      ∑' z, law p (intrinsicSphereEvent G x z j) * law p {ω | Conn G ω z y} := by
  let F := fun (a : Finset V × Finset V) (z : V) =>
    snapshotFrontierCell G x z j a ∩ {ω | Conn G (ω \ ballIncidentEdges G a.1) z y}
  have hcover : longConnectionEvent G x y n ⊆ ⋃ a, ⋃ z, F a z := by
    rintro ω ⟨hc,hd⟩
    obtain ⟨a,ha⟩ := exists_ballSnapshotCell G hloc ω x j
    obtain ⟨z,hz,hfresh,_⟩ := intrinsic_long_connection_fresh G ω x y j 0 hj hc
      (by simpa only [Nat.add_zero] using hjn.trans hd)
    have hz' : z ∈ a.2 \ a.1 := by
      rw [intrinsicSphere_eq_ball_sdiff G _ x j hj,ha.1,ha.2] at hz
      exact_mod_cast hz
    apply Set.mem_iUnion.mpr
    refine ⟨a,Set.mem_iUnion.mpr ⟨z,?_,?_⟩⟩
    · simpa only [snapshotFrontierCell,ite_eq_left hz'] using ha
    · rw [ha.1] at hfresh
      exact hfresh
  have hF (a : Finset V × Finset V) (z : V) :
      law p (F a z) ≤ law p (snapshotFrontierCell G x z j a) * law p {ω | Conn G ω z y} := by
    by_cases hz : z ∈ a.2 \ a.1
    · dsimp only [F]
      rw [snapshotFrontierCell,ite_eq_left hz,ballSnapshotCell_fresh_connection_factor G hloc p x y z j a.1 a.2]
      apply mul_le_mul' le_rfl
      apply measure_mono
      intro ω hω
      exact conn_mono G Set.sdiff_subset hω
    · simp only [F,snapshotFrontierCell,ite_eq_right hz,Set.empty_inter,measure_empty,zero_mul,le_refl]
  calc
    _ ≤ law p (⋃ a, ⋃ z, F a z) := measure_mono hcover
    _ ≤ ∑' a, ∑' z, law p (F a z) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun a => measure_iUnion_le (F a)))
    _ ≤ ∑' a, ∑' z, law p (snapshotFrontierCell G x z j a) * law p {ω | Conn G ω z y} :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (hF a))
    _ = ∑' z, (∑' a, law p (snapshotFrontierCell G x z j a)) * law p {ω | Conn G ω z y} := by
      rw [ENNReal.tsum_comm]
      simp only [ENNReal.tsum_mul_right]
    _ = _ := by
      apply tsum_congr
      intro z
      rw [←measure_iUnion (snapshotFrontierCell_pairwise G x z j)
        (measurableSet_snapshotFrontierCell G hloc x z j),snapshotFrontierCell_iUnion G hloc x z j hj]

end Percolation.BenjaminiSchramm

end OAI

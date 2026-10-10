import OAI.Analysis.CircleDomains.Sobolev.PhysicalSobolevLipschitzCover

namespace OAI

/-! Countable closed Lipschitz pieces for genuinely local continuous W1,2 functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_sobolev_core_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set EuclideanPlane} (hK : IsCompact K) :
    ∃ F : ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (F n) ∧ F n ⊆ K ∧ LipschitzOnWith (64*(n:ℝ≥0)) u (F n)) ∧
      ∀ᵐ p ∂volume, p ∈ K → p ∈ ⋃ n, F n := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  obtain ⟨η, O, hη, hsη, _, hηR, _, hKO, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_ball hR
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness isOpen_ball
    (scalarBallWeakWitness hu hw hLp R).memW1p hη hsη hηR
  have hwc : Continuous w := hη.continuous.mul hu
  have hws : HasCompactSupport w := hsη.mul_right
  have heq (p : EuclideanPlane) (hp : p ∈ K) : w p = u p := by
    dsimp only [w]
    rw [hone p (hKO hp), one_mul]
  obtain ⟨L, hL, hcover⟩ := compact_sobolev_physical_lipschitz_cover hwc hws W
  refine ⟨fun n => L n ∩ K, ?_, ?_⟩
  · intro n
    refine ⟨(hL n).1.inter hK.isClosed, inter_subset_right, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    rw [← heq p hp.2, ← heq q hq.2]
    exact (hL n).2.dist_le_mul _ hp.1 _ hq.1
  · filter_upwards [hcover] with p hp hpK
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨n, hn, hpK⟩

lemma locally_sobolev_closed_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) :
    ∃ K : ℕ × ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (K n) ∧ LipschitzOnWith (64*(n.2:ℝ≥0)) u (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  choose K hK hcover using fun n : ℕ => local_sobolev_core_lipschitz_cover hu hw hLp
    (isCompact_closedBall (0 : EuclideanPlane) n)
  refine ⟨fun n => K n.1 n.2, ?_, ?_⟩
  · intro n
    exact ⟨(hK n.1 n.2).1, (hK n.1 n.2).2.2⟩
  · have hall : ∀ᵐ p ∂volume, ∀ n : ℕ,
        p ∈ closedBall (0 : EuclideanPlane) n → p ∈ ⋃ j, K n j := ae_all_iff.mpr hcover
    filter_upwards [hall] with p hp
    obtain ⟨n, hn⟩ := exists_nat_gt ‖p‖
    have hpK : p ∈ closedBall (0 : EuclideanPlane) n := by
      simpa only [mem_closedBall, dist_zero_right] using hn.le
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hp n hpK)
    exact mem_iUnion.mpr ⟨(n,j), hj⟩

end CircleDomainRigidity

end

end OAI

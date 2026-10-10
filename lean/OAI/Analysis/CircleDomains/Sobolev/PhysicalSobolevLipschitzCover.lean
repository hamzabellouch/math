import OAI.Analysis.CircleDomains.Sobolev.SobolevClosedLipschitzCover

namespace OAI

/-! Transfer closed Lipschitz pieces from real coordinates to the actual Euclidean plane. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma euclideanPlaneCoordinates_lipschitz : LipschitzWith 1 euclideanPlaneCoordinates := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, euclideanPlaneCoordinates_apply, Prod.dist_eq]
  rw [Real.dist_eq, Real.dist_eq, dist_eq_norm, max_le_iff]
  constructor
  · simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (x-y) (0:Fin 2)
  · simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (x-y) (1:Fin 2)

lemma compact_sobolev_physical_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (W : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (K n) ∧ LipschitzOnWith (64*(n:ℝ≥0)) u (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  obtain ⟨K, hK, hcover⟩ := compact_sobolev_closed_lipschitz_cover hu hs W
  refine ⟨fun n => euclideanPlaneCoordinates ⁻¹' K n, ?_, ?_⟩
  · intro n
    refine ⟨(hK n).1.preimage euclideanPlaneCoordinates.continuous, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := (hK n).2.dist_le_mul _ hx _ hy
    simp only [euclideanPlaneCoordinates.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one, one_mul] using euclideanPlaneCoordinates_lipschitz.dist_le_mul x y)
      (by positivity))
  · filter_upwards [euclideanPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae hcover]
      with p hp
    simpa only [mem_iUnion, mem_preimage] using hp

end CircleDomainRigidity

end

end OAI

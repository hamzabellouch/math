import OAI.Analysis.CircleDomains.Sobolev.SobolevJacobianLocality

namespace OAI

/-! Local Sobolev Jacobians are unchanged by compact interior replacements.
A common compact cutoff reduces the assertion to the proved whole-plane
null Lagrangian, while its plateau preserves all four original gradients. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_jacobian_integral_locality
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u U) (hv : DeGiorgi.MemW1pWitness 2 v U)
    (ha : DeGiorgi.MemW1pWitness 2 a U) (hb : DeGiorgi.MemW1pWitness 2 b U)
    (hua : EqOn u a (U \ K)) (hvb : EqOn v b (U \ K)) :
    (∫ x in K, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in K, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  obtain ⟨η, V, hη, hsη, _hunit, hηU, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  have hVU : V ⊆ U := by
    intro x hx
    apply hηU
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  obtain ⟨hu'⟩ := exists_global_compact_cutoff_witness hU hu.memW1p hη hsη hηU
  obtain ⟨hv'⟩ := exists_global_compact_cutoff_witness hU hv.memW1p hη hsη hηU
  obtain ⟨ha'⟩ := exists_global_compact_cutoff_witness hU ha.memW1p hη hsη hηU
  obtain ⟨hb'⟩ := exists_global_compact_cutoff_witness hU hb.memW1p hη hsη hηU
  have heq {f g : EuclideanPlane → ℝ} (hfg : EqOn f g (U \ K)) :
      EqOn (fun x => η x*f x) (fun x => η x*g x) Kᶜ := by
    intro x hx
    change η x*f x = η x*g x
    by_cases hxU : x ∈ U
    · rw [hfg ⟨hxU, hx⟩]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxU (hηU ht)), zero_mul, zero_mul]
  have hj := sobolev_jacobian_integral_locality hu' hv' ha' hb'
    hsη.mul_right hsη.mul_right hK.isClosed (heq hua) (heq hvb)
  have huG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hu hu' hone i)
  have hvG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hv hv' hone i)
  have haG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU ha ha' hone i)
  have hbG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hb hb' hone i)
  calc
    _ = ∫ x in K, hu'.weakGrad x 0 * hv'.weakGrad x 1 -
        hu'.weakGrad x 1 * hv'.weakGrad x 0 := by
      apply integral_congr_ae
      filter_upwards [huG 0, huG 1, hvG 0, hvG 1] with x hu0 hu1 hv0 hv1
      rw [hu0, hu1, hv0, hv1]
    _ = _ := hj
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [haG 0, haG 1, hbG 0, hbG 1] with x ha0 ha1 hb0 hb1
      rw [ha0, ha1, hb0, hb1]

 theorem volume_restrict_closedBall_eq_ball (R : ℝ) :
    volume.restrict (Metric.closedBall (0 : EuclideanPlane) R) =
      volume.restrict (Metric.ball (0 : EuclideanPlane) R) := by
  apply Measure.restrict_congr_set
  have hs : ∀ᵐ x ∂(volume : Measure EuclideanPlane), x ∉ Metric.sphere 0 R := by
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : EuclideanPlane) R)
  filter_upwards [hs] with x hx
  apply propext
  constructor
  · intro hxC
    have hle : dist x 0 ≤ R := hxC
    have hne : dist x 0 ≠ R := hx
    exact lt_of_le_of_ne hle hne
  · intro hx
    exact Metric.ball_subset_closedBall hx

 theorem local_sobolev_jacobian_ball_replacement {R S : ℝ} (hRS : R < S)
    {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 S))
    (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball 0 S))
    (ha : DeGiorgi.MemW1pWitness 2 a (Metric.ball 0 S))
    (hb : DeGiorgi.MemW1pWitness 2 b (Metric.ball 0 S))
    (hua : EqOn u a (Metric.ball 0 S \ Metric.ball 0 R))
    (hvb : EqOn v b (Metric.ball 0 S \ Metric.ball 0 R)) :
    (∫ x in Metric.ball 0 R,
      hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in Metric.ball 0 R,
      ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  have he := local_sobolev_jacobian_integral_locality Metric.isOpen_ball
    (isCompact_closedBall (0 : EuclideanPlane) R) (Metric.closedBall_subset_ball hRS)
    hu hv ha hb
    (fun x hx => hua ⟨hx.1, fun hxB => hx.2 (Metric.ball_subset_closedBall hxB)⟩)
    (fun x hx => hvb ⟨hx.1, fun hxB => hx.2 (Metric.ball_subset_closedBall hxB)⟩)
  simpa only [volume_restrict_closedBall_eq_ball R] using he

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.ModelBarrierGradient
import OAI.Analysis.CircleDomains.Sobolev.L2ThreeTermBound

namespace OAI

/-! Turn the proved reference-comparison bound into the total source
barrier energy. The reference is constructed by conformal transport. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_norm_le_error_add {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f g : X → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm f 2 μ).toReal ≤ (eLpNorm (fun x => f x-g x) 2 μ).toReal+(eLpNorm g 2 μ).toReal := by
  have hd := hf.sub hg
  have hz : MemLp (fun _ : X => (0 : ℝ)) 2 μ := MemLp.zero'
  have h := l2_three_term_bound (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num) le_rfl
    hf.aestronglyMeasurable hd.norm hg.norm hz
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun x => by
      simpa only [one_mul, zero_mul, add_zero, Pi.sub_apply] using (calc
        ‖f x‖ = ‖(f x-g x)+g x‖ := by rw [sub_add_cancel]
        _ ≤ ‖f x-g x‖+‖g x‖ := norm_add_le _ _)))
  have hdn : AEStronglyMeasurable (fun x => f x-g x) μ := hd.aestronglyMeasurable
  have h' : (eLpNorm f 2 μ).toReal ≤
      (eLpNorm (fun x => ‖f x-g x‖) 2 μ).toReal+(eLpNorm (fun x => ‖g x‖) 2 μ).toReal := by
    simpa only [one_mul, zero_mul, add_zero, Pi.sub_apply] using h.2
  rw [eLpNorm_norm _ hdn, eLpNorm_norm _ hg.aestronglyMeasurable] at h'
  exact h'


namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem barrier_energy_from_reference (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ)
    {f : EuclideanPlane → ℝ} (W : DeGiorgi.MemW1pWitness 2 f (physicalPlaneDomain G ∩ ball 0 L))
    {r s : ℝ} (hs0 : 0 ≤ s)
    (henergy : (∫ x : EuclideanPlane, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) ≤ s^2)
    (herror : (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient
      ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ r) :
    (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ r+s := by
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) L
  obtain ⟨V,hV,hVE⟩ := M.smooth_barrier_pullback hG hinf hΦ hs
  have hVr := V.weakGrad_memLp.restrict (ball (0 : EuclideanPlane) L)
  rw [Measure.restrict_restrict measurableSet_ball, inter_comm] at hVr
  have hpart : (∫ x in U, ‖V.weakGrad x‖^2) ≤ s^2 := by
    apply le_trans (setIntegral_mono_set V.weakGrad_norm_memLp.integrable_sq
      (Eventually.of_forall (fun x => sq_nonneg _)) (Eventually.of_forall inter_subset_left))
    exact hVE.trans henergy
  have hn := integral_sq_eq_eLpNorm_toReal_sq hVr.norm
  rw [eLpNorm_norm _ hVr.aestronglyMeasurable] at hn
  have hnorm : (eLpNorm V.weakGrad 2 (volume.restrict U)).toReal ≤ s := by
    rw [hn] at hpart
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm V.weakGrad 2 (volume.restrict U))]
  have hfield := M.reference_barrier_gradient hG hinf L Wx Wy hΦ V hV
  have heq : (fun x => W.weakGrad x-V.weakGrad x) =ᵐ[volume.restrict U]
      (fun x => W.weakGrad x-planeCovectorGradient
        ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
          ((M.function (complexPlaneCoordinates x)).im))).comp
            (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) := by
    filter_upwards [hfield] with x hx
    rw [hx]
  have hdiff : (eLpNorm (fun x => W.weakGrad x-V.weakGrad x) 2 (volume.restrict U)).toReal ≤ r := by
    rw [eLpNorm_congr_ae heq]
    exact herror
  exact (l2_norm_le_error_add W.weakGrad_memLp hVr).trans (add_le_add hdiff hnorm)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI

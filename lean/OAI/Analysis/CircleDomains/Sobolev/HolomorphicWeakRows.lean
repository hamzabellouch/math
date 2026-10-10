import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakGradient
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicScalarEnergy
import OAI.Analysis.CircleDomains.Sobolev.WeakPairL2

namespace OAI

/-! Holomorphic source coordinates have equal row energy. Consequently
controlling the selected horizontal changed-set energy controls the
whole reference differential used by the barrier comparison. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_weak_gradient_norm
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖W.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)‖ := by
  filter_upwards [complex_weak_gradient_ae hD hf hE W] with x hx
  rw [hx, complex_plane_covector_norm]

 theorem holomorphic_weak_rows_norm_eq
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D)
    (hEr : MemLp (fderiv ℝ (fun z => (f z).re)) 2 (volume.restrict D))
    (hEi : MemLp (fderiv ℝ (fun z => (f z).im)) 2 (volume.restrict D))
    (Wr : DeGiorgi.MemW1pWitness 2 (fun x => (f (complexPlaneCoordinates x)).re)
      (complexPlaneCoordinates ⁻¹' D))
    (Wi : DeGiorgi.MemW1pWitness 2 (fun x => (f (complexPlaneCoordinates x)).im)
      (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖Wr.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖Wi.weakGrad x‖ := by
  have hs : ContDiffOn ℝ ∞ f D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hr := complex_weak_gradient_norm hD (Complex.reCLM.contDiff.comp_contDiffOn hs) hEr Wr
  have hi := complex_weak_gradient_norm hD (Complex.imCLM.contDiff.comp_contDiffOn hs) hEi Wi
  filter_upwards [hr,hi,ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hxr hxi hx
  rw [hxr,hxi]
  change ‖fderiv ℝ (fun z => (f z).re) (complexPlaneCoordinates x)‖ =
    ‖fderiv ℝ (fun z => (f z).im) (complexPlaneCoordinates x)‖
  have hd := (hf _ hx).differentiableAt (hD.mem_nhds hx)
  have he := (holomorphic_real_fderiv_norm_sq hd).trans (holomorphic_imag_fderiv_norm_sq hd).symm
  nlinarith [norm_nonneg (fderiv ℝ (fun z => (f z).re) (complexPlaneCoordinates x)),
    norm_nonneg (fderiv ℝ (fun z => (f z).im) (complexPlaneCoordinates x))]

 theorem weak_pair_indicator_bound
    {U S : Set EuclideanPlane} (hS : MeasurableSet S)
    {a b : EuclideanPlane → EuclideanPlane}
    (ha : MemLp a 2 (volume.restrict U)) (hb : MemLp b 2 (volume.restrict U))
    (heq : (fun x => ‖a x‖) =ᵐ[volume.restrict U] fun x => ‖b x‖) :
    (eLpNorm (S.indicator (fun x => ‖weakPairDifferential (a x) (b x)‖)) 2
      (volume.restrict U)).toReal ≤
      2*(eLpNorm (S.indicator (fun x => ‖a x‖)) 2 (volume.restrict U)).toReal := by
  have hA := ha.norm.indicator hS
  have hB := (weakPairDifferential_memLp ha hb).1.norm.indicator hS
  have hz : MemLp (fun _ : EuclideanPlane => (0 : ℝ)) 2 (volume.restrict U) := MemLp.zero'
  have hh := l2_three_term_bound (a := 2) (b := 0) (c := 0) (by norm_num) le_rfl le_rfl
    hB.aestronglyMeasurable hA hz hz
    (Eventually.of_forall (fun x => by exact indicator_nonneg (fun _ _ => norm_nonneg _) x))
    (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) (by
      filter_upwards [heq] with x hx
      by_cases hs : x ∈ S
      · simp only [indicator_of_mem hs, Real.norm_eq_abs, abs_norm, zero_mul, add_zero]
        exact (weakPairDifferential_norm_le _ _).trans (by rw [← hx]; ring_nf; exact le_rfl)
      · simp only [indicator_of_notMem hs, norm_zero, mul_zero, add_zero, le_refl])
  simpa only [zero_mul, add_zero] using hh.2

end CircleDomainRigidity

end

end OAI

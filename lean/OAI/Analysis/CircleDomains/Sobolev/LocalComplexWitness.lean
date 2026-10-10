import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealBeltrami

namespace OAI

/-! The weak complex differential supplies genuine local Sobolev witnesses
for both scalar coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_restrict_from_univ
    {f g : EuclideanPlane → ℝ} {i : Fin 2}
    (h : DeGiorgi.HasWeakPartialDeriv i g f univ) (U : Set EuclideanPlane) :
    DeGiorgi.HasWeakPartialDeriv i g f U := by
  intro φ hφ hs hsub
  have hh := h φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hh
  have hf : ∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun hd => hx (hsub (tsupport_fderiv_apply_subset ℝ _ hd))), mul_zero]
  have hg : ∫ x in U, g x * φ x = ∫ x, g x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsub ht)), mul_zero]
  rw [hf, hg]
  exact hh

 theorem continuous_memLp_ball {f : EuclideanPlane → ℝ} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 (volume.restrict (Metric.ball 0 R)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanPlane) R).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hB ⟨x, Metric.ball_subset_closedBall hx, rfl⟩

namespace PlaneLocalWeakComplex

 def realWitness {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hf : Continuous f) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x => (f x).re) (Metric.ball 0 R) where
  memLp := continuous_memLp_ball (Complex.continuous_re.comp hf) R
  weakGrad := D.realGradient
  weakGrad_component_memLp := D.real_memLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (D.real_weak i) _

 def imagWitness {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hf : Continuous f) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x => (f x).im) (Metric.ball 0 R) where
  memLp := continuous_memLp_ball (Complex.continuous_im.comp hf) R
  weakGrad := D.imagGradient
  weakGrad_component_memLp := D.imag_memLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (D.imag_weak i) _

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI

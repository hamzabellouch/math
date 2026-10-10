import OAI.Analysis.CircleDomains.Topology.BoundedCompactCutoff

namespace OAI

/-! The complement of a unit-bounded scalar has the negative weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complement_weak_gradient
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hw : DeGiorgi.HasWeakGrad G f univ) :
    DeGiorgi.HasWeakGrad (fun x => -G x) (fun x => 1 - f x) univ := by
  intro i φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hd : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun x => fderiv ℝ φ x v) := hs.fderiv_apply (𝕜 := ℝ) v
  have hi : Integrable (fun x => f x * fderiv ℝ φ x v) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_unit_bound hm hf).integrable_smul_right_of_hasCompactSupport hd hds
  have hz := (DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
    (f := fun _ : EuclideanPlane => (1 : ℝ)) contDiff_const) φ hφ hs hsub
  simp only [fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero,
    one_mul, Measure.restrict_univ] at hz
  have h := hw i φ hφ hs hsub
  simp only [Measure.restrict_univ] at h ⊢
  change (∫ x, (1 - f x) * fderiv ℝ φ x v) = -(∫ x, -(G x i) * φ x)
  simp only [sub_mul, one_mul, neg_mul, integral_neg]
  rw [integral_sub (hd.integrable_of_hasCompactSupport hds) hi]
  change (∫ x, fderiv ℝ φ x v) = 0 at hz
  change (∫ x, f x * fderiv ℝ φ x v) = -(∫ x, G x i * φ x) at h
  linarith

end CircleDomainRigidity

end

end OAI

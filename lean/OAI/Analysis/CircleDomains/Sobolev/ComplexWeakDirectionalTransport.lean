import OAI.Analysis.CircleDomains.Sobolev.ComplexSobolevTransport
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! Transport a complex distributional directional derivative to each real
component of the physical weak gradient. Only smooth compact tests and
local integrability enter this bridge. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma weakPartial_of_complex_directional_identity
    {f V : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    (hV : LocallyIntegrable V volume) (i : Fin 2) (v : ℂ)
    (hv : complexPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : SchwartzMap ℂ ℂ, HasCompactSupport (ψ : ℂ → ℂ) →
      (∫ z, ψ z * V z) = -(∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * f z))
    (L : ℂ →L[ℝ] ℝ) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => L (V (complexPlaneCoordinates x)))
      (fun x => L (f (complexPlaneCoordinates x))) univ := by
  intro φ hφ hs _
  let e := complexPlaneCoordinates
  let ψ : ℂ → ℂ := fun z => ((φ (e.symm z) : ℝ) : ℂ)
  have hψ : ContDiff ℝ (↑(⊤ : ENat)) ψ :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp e.symm.contDiff)
  have hsψ : HasCompactSupport ψ :=
    (hs.comp_homeomorph e.symm.toHomeomorph).comp_left Complex.ofReal_zero
  let Φ : SchwartzMap ℂ ℂ := hsψ.toSchwartzMap hψ
  have hd (z : ℂ) : fderiv ℝ ψ z v =
      ((fderiv ℝ φ (e.symm z) (EuclideanSpace.single i 1) : ℝ) : ℂ) := by
    rw [show ψ = Complex.ofRealCLM ∘ (φ ∘ e.symm) from rfl,
      fderiv_comp z Complex.ofRealCLM.differentiableAt
        ((hφ.differentiable (by simp)).comp e.symm.differentiable).differentiableAt,
      Complex.ofRealCLM.fderiv,
      fderiv_comp z (hφ.differentiable (by simp)).differentiableAt
        e.symm.differentiableAt, e.symm.fderiv]
    change ((fderiv ℝ φ (e.symm z) (e.symm v) : ℝ) : ℂ) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hderiv : Continuous (fun z => fderiv ℝ ψ z v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsderiv : HasCompactSupport (fun z => fderiv ℝ ψ z v) :=
    hsψ.fderiv_apply ℝ v
  have hintV : Integrable (fun z => ψ z * V z) volume := by
    simpa only [smul_eq_mul] using
      hV.integrable_smul_left_of_hasCompactSupport hψ.continuous hsψ
  have hintf : Integrable (fun z => fderiv ℝ ψ z v * f z) volume := by
    simpa only [smul_eq_mul] using
      hf.integrable_smul_left_of_hasCompactSupport hderiv hsderiv
  have hw := congrArg L (hweak Φ hsψ)
  change L (∫ z, ψ z * V z) = L (-(∫ z, fderiv ℝ ψ z v * f z)) at hw
  rw [map_neg, ← L.integral_comp_comm hintV, ← L.integral_comp_comm hintf] at hw
  have ht (g : ℂ → ℝ) : (∫ x, g (e x)) = ∫ z, g z :=
    complexPlaneCoordinates_measurePreserving.integral_comp
      e.toHomeomorph.measurableEmbedding g
  have hVtransport : (∫ z, L (ψ z * V z)) =
      ∫ x, L (V (e x)) * φ x := by
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ψ, ContinuousLinearEquiv.symm_apply_apply]
    rw [← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
  have hftransport : (∫ z, L (fderiv ℝ ψ z v * f z)) =
      ∫ x, L (f (e x)) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hd, ContinuousLinearEquiv.symm_apply_apply, ← Complex.real_smul,
      map_smul, smul_eq_mul, mul_comm]
  rw [hVtransport, hftransport] at hw
  simp only [Measure.restrict_univ]
  linarith

end CircleDomainRigidity

end

end OAI

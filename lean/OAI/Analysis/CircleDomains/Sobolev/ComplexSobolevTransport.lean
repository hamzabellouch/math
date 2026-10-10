import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates
import OAI.Analysis.KLS.Sobolev.Witnesses

namespace OAI

/-! The two physical complex-coordinate derivative identities give the
Euclidean-plane weak derivatives, with the same area measure. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

@[simp] theorem complexPlaneCoordinates_zero :
    complexPlaneCoordinates (EuclideanSpace.single 0 1) = 1 := by
  simp only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    euclideanPlaneCoordinates_single_zero]
  apply Complex.ext <;> rfl

@[simp] theorem complexPlaneCoordinates_one :
    complexPlaneCoordinates (EuclideanSpace.single 1 1) = Complex.I := by
  simp only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    euclideanPlaneCoordinates_single_one]
  apply Complex.ext <;> rfl

theorem complexPlaneCoordinates_measurePreserving :
    MeasurePreserving complexPlaneCoordinates volume volume :=
  (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
    euclideanPlaneCoordinates_measurePreserving

theorem weakPartial_of_complex_identity
    {f G : ℂ → ℝ} (i : Fin 2) (v : ℂ)
    (hv : complexPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ z, f z * fderiv ℝ ψ z v) = -(∫ z, G z * ψ z))
    (U : Set ℂ) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ complexPlaneCoordinates)
      (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' U) := by
  intro φ hφ hs hsub
  let e := complexPlaneCoordinates
  let ψ : ℂ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ 1 ψ := (hφ.comp e.symm.contDiff).of_le (by simp)
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hd (z : ℂ) : fderiv ℝ ψ z v =
      fderiv ℝ φ (e.symm z) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp z (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change fderiv ℝ φ (e.symm z) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hleft : ∀ x, x ∉ e ⁻¹' U →
      (f ∘ e) x * fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hnx : x ∉ tsupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      fun h => hx (hsub ((tsupport_fderiv_apply_subset ℝ _ ) h))
    rw [image_eq_zero_of_notMem_tsupport hnx, mul_zero]
  have hright : ∀ x, x ∉ e ⁻¹' U → (G ∘ e) x * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  have he : MeasurePreserving e volume volume := complexPlaneCoordinates_measurePreserving
  calc
    _ = ∫ x, f (e x) * fderiv ℝ ψ (e x) v := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [hd, ContinuousLinearEquiv.symm_apply_apply, comp_apply]
    _ = ∫ z, f z * fderiv ℝ ψ z v :=
      he.integral_comp e.toHomeomorph.measurableEmbedding (fun z => f z * fderiv ℝ ψ z v)
    _ = -(∫ z, G z * ψ z) := hweak ψ hψ hsψ
    _ = _ := by
      rw [← he.integral_comp e.toHomeomorph.measurableEmbedding (fun z => G z * ψ z)]
      simp only [ψ, comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI

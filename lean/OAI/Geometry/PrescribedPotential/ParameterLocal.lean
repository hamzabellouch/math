import Mathlib
import OAI.Geometry.PrescribedPotential.ParameterResolvent
import OAI.Geometry.PrescribedPotential.VariablePoisson

namespace OAI

/-! Parameter Local. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Real

namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma parameter_resolvent_perturbation_bound (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (m : ℝ) (hm : 1 ≤ m)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ) :
    ‖perturbation v a ∘L parameterHilbert H hH m hm‖ ≤
      perturbationBound v a * ellipticBound H hH := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (perturbationBound_nonneg v a) (ellipticBound_pos H hH).le)
  intro u
  change ‖perturbation v a (parameterHilbert H hH m hm u)‖ ≤ _
  calc
    _ ≤ perturbationBound v a * ‖parameterHilbert H hH m hm u‖ := perturbation_bound _ _ _
    _ ≤ perturbationBound v a * (ellipticBound H hH * ‖u‖) :=
      mul_le_mul_of_nonneg_left (parameterHilbert_bound H hH m hm u)
        (perturbationBound_nonneg v a)
    _ = _ := by ring

def parameterCorrection (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) :
    L2 (EC n) →L[ℂ] L2 (EC n) :=
  ↑((Units.oneSub (perturbation v a ∘L parameterHilbert H hH m hm)
    ((parameter_resolvent_perturbation_bound H hH m hm v a).trans_lt hsmall))⁻¹)

lemma parameterCorrection_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    parameterCorrection H hH m hm v a hsmall f -
      perturbation v a (parameterHilbert H hH m hm
        (parameterCorrection H hH m hm v a hsmall f)) = f := by
  let U := Units.oneSub (perturbation v a ∘L parameterHilbert H hH m hm)
    ((parameter_resolvent_perturbation_bound H hH m hm v a).trans_lt hsmall)
  change ((↑U : L2 (EC n) →L[ℂ] L2 (EC n)) * ↑U⁻¹) f = f
  rw [Units.mul_inv, _root_.one_apply_eq_self]

lemma parameterCorrection_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    ‖parameterCorrection H hH m hm v a hsmall f‖ ≤
      ‖f‖ / (1 - perturbationBound v a * ellipticBound H hH) := by
  let u := parameterCorrection H hH m hm v a hsmall f
  have he : u = f + perturbation v a (parameterHilbert H hH m hm u) :=
    sub_eq_iff_eq_add.mp (parameterCorrection_equation H hH m hm v a hsmall f)
  have hb : ‖u‖ ≤ ‖f‖ + (perturbationBound v a * ellipticBound H hH) * ‖u‖ := by
    calc
      _ = ‖f + perturbation v a (parameterHilbert H hH m hm u)‖ := congrArg norm he
      _ ≤ ‖f‖ + ‖perturbation v a (parameterHilbert H hH m hm u)‖ := norm_add_le _ _
      _ ≤ ‖f‖ + perturbationBound v a * ‖parameterHilbert H hH m hm u‖ :=
        add_le_add le_rfl (perturbation_bound v a (parameterHilbert H hH m hm u))
      _ ≤ ‖f‖ + perturbationBound v a * (ellipticBound H hH * ‖u‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (parameterHilbert_bound H hH m hm u)
          (perturbationBound_nonneg v a))
      _ = _ := by ring
  change ‖u‖ ≤ _
  rw [le_div_iff₀ (sub_pos.mpr hsmall)]
  linarith

def parameterLocal (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) :
    L2 (EC n) →L[ℂ] L2 (EC n) :=
  parameterHilbert H hH m hm ∘L parameterCorrection H hH m hm v a hsmall

lemma parameterLocal_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    ‖parameterLocal H hH m hm v a hsmall f‖ ≤
      (ellipticBound H hH / (1 - perturbationBound v a * ellipticBound H hH)) * ‖f‖ := by
  change ‖parameterHilbert H hH m hm (parameterCorrection H hH m hm v a hsmall f)‖ ≤ _
  apply (parameterHilbert_bound H hH m hm _).trans
  calc
    _ ≤ ellipticBound H hH * (‖f‖ / (1 - perturbationBound v a * ellipticBound H hH)) :=
      mul_le_mul_of_nonneg_left (parameterCorrection_bound H hH m hm v a hsmall f)
        (ellipticBound_pos H hH).le
    _ = _ := by ring

lemma parameterLocal_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    (m^2 : ℂ) • realize 2 (parameterLocal H hH m hm v a hsmall f) -
      frozenDifferential H (realize 2 (parameterLocal H hH m hm v a hsmall f)) -
      (perturbation v a (parameterLocal H hH m hm v a hsmall f) : 𝓢'(EC n, ℂ)) =
      (f : 𝓢'(EC n, ℂ)) := by
  let u := parameterCorrection H hH m hm v a hsmall f
  change (m^2 : ℂ) • realize 2 (parameterHilbert H hH m hm u) -
    frozenDifferential H (realize 2 (parameterHilbert H hH m hm u)) -
      (perturbation v a (parameterHilbert H hH m hm u) : 𝓢'(EC n, ℂ)) = _
  rw [parameterHilbert_equation]
  simpa only [map_sub, Lp.toTemperedDistributionCLM_apply] using
    congrArg (Lp.toTemperedDistributionCLM ℂ volume 2)
      (parameterCorrection_equation H hH m hm v a hsmall f)

 
def parameterLocalZero (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) :
    L2 (EC n) →L[ℂ] L2 (EC n) :=
  parameterZero H hH m (lt_of_lt_of_le zero_lt_one hm) ∘L
    parameterCorrection H hH m hm v a hsmall

lemma parameterLocalZero_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    (parameterLocalZero H hH m hm v a hsmall f : 𝓢'(EC n, ℂ)) =
      realize 2 (parameterLocal H hH m hm v a hsmall f) := by
  dsimp only [parameterLocalZero, parameterLocal, ContinuousLinearMap.comp_apply]
  rw [parameterZero_distribution]
  have h := parameterHilbert_realize H hH m hm 0
    (parameterCorrection H hH m hm v a hsmall f)
  simpa only [zero_add, realize, neg_zero, besselPotential_zero,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Lp.toTemperedDistributionCLM_apply] using h.symm

lemma parameterLocalZero_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    ‖parameterLocalZero H hH m hm v a hsmall f‖ ≤
      ((m^2)⁻¹ / (1 - perturbationBound v a * ellipticBound H hH)) * ‖f‖ := by
  apply (parameterZero_bound H hH m (lt_of_lt_of_le zero_lt_one hm) _).trans
  calc
    _ ≤ (m^2)⁻¹ * (‖f‖ / (1 - perturbationBound v a * ellipticBound H hH)) :=
      mul_le_mul_of_nonneg_left (parameterCorrection_bound H hH m hm v a hsmall f) (by positivity)
    _ = _ := by ring

def parameterLocalFirst (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (w : EC n) :
    L2 (EC n) →L[ℂ] L2 (EC n) :=
  parameterFirst H hH m hm w ∘L parameterCorrection H hH m hm v a hsmall

lemma parameterLocalFirst_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (w : EC n) (f : L2 (EC n)) :
    (parameterLocalFirst H hH m hm v a hsmall w f : 𝓢'(EC n, ℂ)) =
      ∂_{w} (realize 2 (parameterLocal H hH m hm v a hsmall f)) := by
  dsimp only [parameterLocalFirst, ContinuousLinearMap.comp_apply]
  rw [parameterFirst_distribution, ← parameterLocalZero_distribution,
    parameterLocalZero, ContinuousLinearMap.comp_apply, parameterZero_distribution]

lemma parameterLocalFirst_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (w : EC n) (f : L2 (EC n)) :
    ‖parameterLocalFirst H hH m hm v a hsmall w f‖ ≤
      ((2 * Real.pi * ‖w‖ * ellipticBound H hH) /
        (m * (1 - perturbationBound v a * ellipticBound H hH))) * ‖f‖ := by
  apply (parameterFirst_bound H hH m hm w _).trans
  calc
    _ ≤ ((2 * Real.pi * ‖w‖ * ellipticBound H hH) / m) *
        (‖f‖ / (1 - perturbationBound v a * ellipticBound H hH)) :=
      mul_le_mul_of_nonneg_left (parameterCorrection_bound H hH m hm v a hsmall f)
        (by positivity [ellipticBound_pos H hH])
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end FrozenPoisson

end
end

end OAI

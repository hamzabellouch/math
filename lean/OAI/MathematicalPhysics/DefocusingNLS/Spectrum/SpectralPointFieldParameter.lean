import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCorrectionParameter
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The pointwise parameter derivative of the normalized spectral equation. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularPointFieldCLM (νp νm η : ℂ) (m : ℕ) (q : ℂ) : E₄ →L[ℂ] E₄ :=
  LinearMap.toContinuousLinearMap
    { toFun := circularBoundedField νp νm η m q
      map_add' := circularBoundedField_add νp νm η m q
      map_smul' := fun a v => circularBoundedField_smul νp νm η m q a v }

noncomputable def circularPointLeadingCLM (t : ℝ) : E₄ →L[ℂ] E₄ :=
  LinearMap.toContinuousLinearMap
    { toFun := circularLeadingField t
      map_add' := circularLeadingField_add t
      map_smul' := fun a v => circularLeadingField_smul t a v }

noncomputable def circularPointSlopeCLM (νp νm z : ℂ) : E₄ →L[ℂ] E₄ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        ((0, 4 * v.1.2 + (4 * (νp - 2 * z) + 20) * v.1.1),
         (0, 4 * v.2.2 + (4 * (νm - 2 * z) + 20) * v.2.1))
      map_add' := by
        intro v w
        apply Prod.ext <;> apply Prod.ext <;> simp [mul_add] <;> ring
      map_smul' := by
        intro a v
        apply Prod.ext <;> apply Prod.ext <;> simp [smul_eq_mul] <;> ring }

theorem circularPointFieldCLM_hasParameterDerivAt (νp νm η : ℂ) (m : ℕ)
    (q z : ℂ) :
    HasDerivAt (fun lam => circularPointFieldCLM (νp - 2 * lam) (νm - 2 * lam) η m q)
      (circularPointSlopeCLM νp νm z) z := by
  have he (lam : ℂ) :
      circularPointFieldCLM (νp - 2 * lam) (νm - 2 * lam) η m q =
        circularPointFieldCLM νp νm η m q +
          (lam / 2) • (circularPointFieldCLM (νp - 2) (νm - 2) η m q -
            circularPointFieldCLM (νp + 2) (νm + 2) η m q) +
          (lam ^ 2 / 2) • (circularPointFieldCLM (νp - 2) (νm - 2) η m q +
            circularPointFieldCLM (νp + 2) (νm + 2) η m q -
            (2 : ℂ) • circularPointFieldCLM νp νm η m q) := by
    apply ContinuousLinearMap.ext
    intro v
    exact circularBoundedField_shift_eq νp νm η lam m q v
  simp_rw [he]
  have h1 := (hasDerivAt_id z).div_const (2 : ℂ)
  have h2 : HasDerivAt (fun lam : ℂ => lam ^ 2 / 2) z z := by
    apply (((hasDerivAt_id z).pow 2).div_const (2 : ℂ)).congr_deriv
    simp only [id_eq]
    ring
  have hh := ((hasDerivAt_const z (circularPointFieldCLM νp νm η m q)).add
    (h1.smul_const (circularPointFieldCLM (νp - 2) (νm - 2) η m q -
      circularPointFieldCLM (νp + 2) (νm + 2) η m q))).add
    (h2.smul_const (circularPointFieldCLM (νp - 2) (νm - 2) η m q +
      circularPointFieldCLM (νp + 2) (νm + 2) η m q -
      (2 : ℂ) • circularPointFieldCLM νp νm η m q))
  apply hh.congr_deriv
  apply ContinuousLinearMap.ext
  intro v
  change (0 : E₄) + (1 / 2 : ℂ) •
      (circularBoundedField (νp - 2) (νm - 2) η m q v -
        circularBoundedField (νp + 2) (νm + 2) η m q v) +
      z • (circularBoundedField (νp - 2) (νm - 2) η m q v +
        circularBoundedField (νp + 2) (νm + 2) η m q v -
        (2 : ℂ) • circularBoundedField νp νm η m q v) =
      ((0, 4 * v.1.2 + (4 * (νp - 2 * z) + 20) * v.1.1),
       (0, 4 * v.2.2 + (4 * (νm - 2 * z) + 20) * v.2.1))
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [circularBoundedField, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

theorem circularPointField_hasParameterDerivAt (νp νm η : ℂ) (m : ℕ)
    (q z : ℂ) (v : ℂ → E₄) (dv : E₄) (hv : HasDerivAt v dv z) :
    HasDerivAt (fun lam => circularBoundedField (νp - 2 * lam) (νm - 2 * lam) η m q (v lam))
      (circularBoundedField (νp - 2 * z) (νm - 2 * z) η m q dv +
        circularPointSlopeCLM νp νm z (v z)) z := by
  have hh := (circularPointFieldCLM_hasParameterDerivAt νp νm η m q z).clm_apply hv
  convert! hh using 1
  exact add_comm _ _

theorem circularPointLeading_hasParameterDerivAt (t : ℝ) (v : ℂ → E₄)
    (dv : E₄) (z : ℂ) (hv : HasDerivAt v dv z) :
    HasDerivAt (fun lam => circularLeadingField t (v lam)) (circularLeadingField t dv) z := by
  exact (circularPointLeadingCLM t).hasFDerivAt.comp_hasDerivAt z hv

theorem circularPointSlope_tail (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (z : ℂ) (v : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (circularFieldParameterSlope νp νm η m hm q z v) t =
      circularPointSlopeCLM νp νm z (circularTailEvaluation v t) :=
  circularFieldParameterSlope_evaluation νp νm η m hm q z v t

end DefocusingNLS

end OAI

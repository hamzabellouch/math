import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnalyticCorrection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicOutgoing

namespace OAI

/-! Differentiating the actual outgoing correction in its weighted Banach
space. This retains the source term needed for generalized eigenvectors. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

local instance : IsBoundedSMul ℂ (CircularTailSpace →L[ℂ] CircularTailSpace) := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℂ)
    (E := CircularTailSpace →L[ℂ] CircularTailSpace))

noncomputable def circularFieldParameterSlope (νp νm η : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (z : ℂ) : CircularTailSpace →L[ℂ] CircularTailSpace :=
  (1 / 2 : ℂ) • (circularFieldOperator (νp - 2) (νm - 2) η m hm q -
      circularFieldOperator (νp + 2) (νm + 2) η m hm q) +
    z • (circularFieldOperator (νp - 2) (νm - 2) η m hm q +
      circularFieldOperator (νp + 2) (νm + 2) η m hm q -
      (2 : ℂ) • circularFieldOperator νp νm η m hm q)

theorem circularFieldParameterSlope_evaluation (νp νm η : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (z : ℂ) (v : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (circularFieldParameterSlope νp νm η m hm q z v) t =
      ((0, 4 * (circularTailEvaluation v t).1.2 +
        (4 * (νp - 2 * z) + 20) * (circularTailEvaluation v t).1.1),
       (0, 4 * (circularTailEvaluation v t).2.2 +
        (4 * (νm - 2 * z) + 20) * (circularTailEvaluation v t).2.1)) := by
  change (1 / 2 : ℂ) •
      (circularBoundedField (νp - 2) (νm - 2) η m (q t) (circularTailEvaluation v t) -
       circularBoundedField (νp + 2) (νm + 2) η m (q t) (circularTailEvaluation v t)) +
    z • (circularBoundedField (νp - 2) (νm - 2) η m (q t) (circularTailEvaluation v t) +
      circularBoundedField (νp + 2) (νm + 2) η m (q t) (circularTailEvaluation v t) -
      (2 : ℂ) • circularBoundedField νp νm η m (q t) (circularTailEvaluation v t)) = _
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [circularBoundedField, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

theorem circularFieldOperator_hasParameterDerivAt (νp νm η : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (z : ℂ) :
    HasDerivAt (fun lam => circularFieldOperator (νp - 2 * lam) (νm - 2 * lam) η m hm q)
      (circularFieldParameterSlope νp νm η m hm q z) z := by
  simp_rw [circularFieldOperator_shift_eq]
  have h1 := (hasDerivAt_id z).div_const (2 : ℂ)
  have h2 : HasDerivAt (fun lam : ℂ => lam ^ 2 / 2) z z := by
    apply (((hasDerivAt_id z).pow 2).div_const (2 : ℂ)).congr_deriv
    simp only [id_eq]
    ring
  have hh := ((hasDerivAt_const z (circularFieldOperator νp νm η m hm q)).add
    (h1.smul_const (circularFieldOperator (νp - 2) (νm - 2) η m hm q -
      circularFieldOperator (νp + 2) (νm + 2) η m hm q))).add
    (h2.smul_const (circularFieldOperator (νp - 2) (νm - 2) η m hm q +
      circularFieldOperator (νp + 2) (νm + 2) η m hm q -
      (2 : ℂ) • circularFieldOperator νp νm η m hm q))
  simp only [zero_add, id_eq, one_div] at hh
  convert! hh using 1
  simp only [circularFieldParameterSlope, one_div]

theorem circularResolvedCorrection_parameter_equation (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (z : ℂ) (hr : AnalyticAt ℂ r z)
    (hgap : circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < κ) :
    let v := circularResolvedCorrection κ hκ νp νm η m hm q r
    deriv v z = circularTailCLM κ hκ
      (circularFieldOperator (νp - 2 * z) (νm - 2 * z) η m hm q (deriv v z) +
        circularFieldParameterSlope νp νm η m hm q z (v z) + deriv r z) := by
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r
  have hv : HasDerivAt v (deriv v z) z :=
    (circularResolvedCorrection_analyticAt κ hκ νp νm η m hm q r z hr hgap).differentiableAt.hasDerivAt
  have hf := ((circularFieldOperator_hasParameterDerivAt νp νm η m hm q z).clm_apply hv).add
    hr.differentiableAt.hasDerivAt
  have hk := (circularTailCLM κ hκ).hasFDerivAt.comp_hasDerivAt z hf
  have hg : Continuous (fun lam : ℂ => circularFieldBound (νp - 2 * lam)
      (νm - 2 * lam) η m ‖q‖) := by unfold circularFieldBound; fun_prop
  have he : v =ᶠ[𝓝 z] fun lam => circularTailCLM κ hκ
      (circularFieldOperator (νp - 2 * lam) (νm - 2 * lam) η m hm q (v lam) + r lam) := by
    filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hgap)] with lam hlam
    exact circularCorrectionResolvent_solve κ hκ νp νm η m hm q lam hlam (r lam)
  have hd := hv.unique (hk.congr_of_eventuallyEq he)
  change deriv v z = circularTailCLM κ hκ
    (circularFieldOperator (νp - 2 * z) (νm - 2 * z) η m hm q (deriv v z) +
      circularFieldParameterSlope νp νm η m hm q z (v z) + deriv r z)
  calc
    deriv v z = circularTailCLM κ hκ
        (circularFieldParameterSlope νp νm η m hm q z (v z) +
          circularFieldOperator (νp - 2 * z) (νm - 2 * z) η m hm q (deriv v z) +
          deriv r z) := by convert! hd using 1
    _ = _ := by congr 1; abel

theorem circularResolvedCorrection_parameter_time_equation (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (z : ℂ) (hr : AnalyticAt ℂ r z)
    (hgap : circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < κ) (t : ℝ) :
    let v := circularResolvedCorrection κ hκ νp νm η m hm q r
    let dv := deriv v z
    HasDerivAt (circularTailEvaluation dv)
      (κ • circularTailEvaluation dv t + circularLeadingField t (circularTailEvaluation dv t) +
        circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t) (circularTailEvaluation dv t) +
        circularTailEvaluation (circularFieldParameterSlope νp νm η m hm q z (v z) +
          deriv r z) t) t := by
  let v := circularResolvedCorrection κ hκ νp νm η m hm q r
  let dv := deriv v z
  let B := circularFieldOperator (νp - 2 * z) (νm - 2 * z) η m hm q
  let f := circularFieldParameterSlope νp νm η m hm q z (v z) + deriv r z
  have he : circularTail κ hκ (B dv + f) = dv := by
    have hh := circularResolvedCorrection_parameter_equation κ hκ νp νm η m hm q r z hr hgap
    simp only [add_assoc] at hh
    convert! hh.symm using 1
  have hd := circularTail_hasDerivAt κ hκ (B dv + f) t
  dsimp only at hd
  rw [he] at hd
  apply hd.congr_deriv
  have hB := circularFieldOperator_evaluation (νp - 2 * z) (νm - 2 * z) η m hm q dv t
  change circularTailEvaluation (B dv) t = _ at hB
  rw [← hB]
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [v, dv, f, circularTailEvaluation, circularLeadingField, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, BoundedContinuousFunction.add_apply]
    abel

theorem circularUnweight_hasParameterDerivAt (κ t : ℝ)
    (v : ℂ → CircularTailSpace) (dv : CircularTailSpace) (z : ℂ)
    (hv : HasDerivAt v dv z) :
    HasDerivAt (fun lam => circularUnweight κ (v lam) t) (circularUnweight κ dv t) z := by
  have he := (circularTailEvaluationCLM t).hasFDerivAt.comp_hasDerivAt z hv
  have hh := he.const_smul (Real.exp (-κ * t) : ℂ)
  convert! hh using 1

theorem circularResolvedCorrection_parameter_unweight_equation (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (r : ℂ → CircularTailSpace) (z : ℂ) (hr : AnalyticAt ℂ r z)
    (hgap : circularFieldBound (νp - 2 * z) (νm - 2 * z) η m ‖q‖ < κ) (t : ℝ) :
    let v := circularResolvedCorrection κ hκ νp νm η m hm q r
    let dv := deriv v z
    HasDerivAt (circularUnweight κ dv)
      (circularLeadingField t (circularUnweight κ dv t) +
        circularBoundedField (νp - 2 * z) (νm - 2 * z) η m (q t) (circularUnweight κ dv t) +
        Real.exp (-κ * t) • circularTailEvaluation
          (circularFieldParameterSlope νp νm η m hm q z (v z) + deriv r z) t) t := by
  exact circularUnweight_hasDerivAt κ t (νp - 2 * z) (νm - 2 * z) η m (q t) _ _
    (circularResolvedCorrection_parameter_time_equation κ hκ νp νm η m hm q r z hr hgap t)

end DefocusingNLS

end OAI

import OAI.Analysis.Mahler.BasisContinuousWedge

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma differentiableAt_formCoefficient [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] {A : E → E [⋀^ι]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : ι → E) (c : ℂ) :
    DifferentiableAt ℝ (fun y => A y v / c) x := by
  simpa only [div_eq_mul_inv, Function.comp_def, ContinuousAlternatingMap.apply_apply] using
    ((ContinuousAlternatingMap.apply ℝ E ℂ v).differentiableAt.comp x hA).mul_const c⁻¹

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma fderiv_formCoefficient [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] {A : E → E [⋀^ι]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : ι → E) (c : ℂ) (u : E) :
    fderiv ℝ (fun y => A y v / c) x u = fderiv ℝ A x u v / c := by
  have h := ((ContinuousAlternatingMap.apply ℝ E ℂ v).hasFDerivAt.comp x
    hA.hasFDerivAt).mul_const c⁻¹
  simpa only [div_eq_mul_inv, Function.comp_def, ContinuousAlternatingMap.apply_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm] using
    congrArg (fun L : E →L[ℝ] ℂ => L u) h.fderiv

lemma differentiableAt_basisContinuousWedge (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^ι]→L[ℝ] ℂ} {B : E → E [⋀^κ]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x := by
  unfold basisContinuousWedge
  exact DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun r _ =>
    ((differentiableAt_formCoefficient hA _ _).mul
      (differentiableAt_formCoefficient hB _ _)).smul_const _))

/-- The Frechet product rule for the continuous, actual shuffle wedge. -/
theorem fderiv_basisContinuousWedge (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^ι]→L[ℝ] ℂ} {B : E → E [⋀^κ]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (u : E) :
    fderiv ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x u =
      basisContinuousWedge basis (fderiv ℝ A x u) (B x) +
      basisContinuousWedge basis (A x) (fderiv ℝ B x u) := by
  have hc (q : ι → J) (r : κ → J) :=
    ((differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ)).mul
      (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))).smul_const
        (continuousCovectorVolume (Sum.elim (complexCoord basis ∘ q) (complexCoord basis ∘ r)))
  simp only [Pi.mul_apply] at hc
  unfold basisContinuousWedge
  rw [fderiv_fun_sum (u := Finset.univ) (fun q _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ => hc q r))]
  simp only [_root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fderiv_fun_sum (u := Finset.univ) (fun r _ => hc q r)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  have hm := (differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ)).mul
    (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))
  change DifferentiableAt ℝ (fun y =>
    (A y (basis ∘ q) / ((Fintype.card ι).factorial : ℂ)) *
    (B y (basis ∘ r) / ((Fintype.card κ).factorial : ℂ))) x at hm
  rw [fderiv_smul_const hm]
  rw [fderiv_fun_mul (differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ))
    (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply,
    _root_.smul_apply, fderiv_formCoefficient hA,
    fderiv_formCoefficient hB, smul_eq_mul, add_smul]
  rw [add_comm]
  congr 1 ; congr 1 ; ring

end Mahler

end OAI

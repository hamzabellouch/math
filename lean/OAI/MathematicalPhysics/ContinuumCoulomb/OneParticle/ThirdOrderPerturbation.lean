import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SharpBlockPerturbation

namespace OAI

/-! A third-order block estimate. Keeping the high-block correction in the
effective form makes simultaneous three-body gadgets have a decreasing error. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace

variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def thirdOrderForm (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) : ℝ := effectiveForm C T B p + ⟪T (B p),D (T (B p))⟫_ℝ

theorem thirdOrder_square_identity (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ) (p : L) (q : H) :
    lowBlockEnergy C A D B p q = thirdOrderForm C T D B p +
      penaltyForm A (q+T (B p)) + ⟪q+T (B p),D (q+T (B p))⟫_ℝ -
        2*⟪q+T (B p),D (T (B p))⟫_ℝ := by
  have hi := penalty_square_identity A T B hAT hAsymm p q (by norm_num : (1:ℝ) ≠ 0)
  simp only [one_mul,inv_one,one_smul] at hi
  have hc : ⟪T (B p),D q⟫_ℝ = ⟪q,D (T (B p))⟫_ℝ := by
    rw [hDsymm,real_inner_comm]
  simp only [map_add,inner_add_left,inner_add_right,hc]
  unfold lowBlockEnergy blockEnergy thirdOrderForm effectiveForm
  linarith

private theorem quadratic_cross_bound {g d x z : ℝ} (hg : 0 < g) :
    -(2*d^2/g)*z^2 ≤ g/2*x^2-2*d*x*z := by
  apply (mul_le_mul_iff_right₀ hg).mp
  field_simp
  nlinarith [sq_nonneg (g*x-2*d*z)]

theorem thirdOrder_energy_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ} (hg : 0 < g)
    (_hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖) (hD : ‖D‖ ≤ d)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ thirdOrderForm C T D B p)
    (p : L) (q : H) :
    -(2*d^2/g+2*m)*η^2*‖p‖^2 ≤
      lowBlockEnergy C A D B p q-μ*(‖p‖^2+‖q‖^2) := by
  let z := T (B p)
  let y := q+z
  have hi := thirdOrder_square_identity C A T D B hAT hAsymm hDsymm p q
  have hnorm := norm_add_sq_two y (-z)
  have hyz : y+(-z) = q := by dsimp [y]; abel
  rw [hyz,norm_neg] at hnorm
  have hz : ‖z‖^2 ≤ η^2*‖p‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  have hdq : -(d*‖y‖^2) ≤ ⟪y,D y⟫_ℝ := by
    have h := highPerturbation_abs_le D (g := 1) (ε := d) (by simpa using hD) y
    simpa using (abs_le.mp h).1
  have hDz : ‖D z‖ ≤ d*‖z‖ :=
    (D.le_opNorm z).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hcross : ⟪y,D z⟫_ℝ ≤ ‖y‖*d*‖z‖ := by
    calc
      _ ≤ ‖y‖*‖D z‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖*(d*‖z‖) := mul_le_mul_of_nonneg_left hDz (norm_nonneg _)
      _ = _ := by ring
  have hquad := quadratic_cross_bound (d := d) (x := ‖y‖) (z := ‖z‖) hg
  have hscale := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖y‖)
  have hμq := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖q‖)
  have hmnorm := mul_le_mul_of_nonneg_left hnorm hm
  have hK : 0 ≤ 2*d^2/g+2*m := by positivity
  have hKz := mul_le_mul_of_nonneg_left hz hK
  have hgp := hgap y
  have hmp := hmin p
  change lowBlockEnergy C A D B p q = thirdOrderForm C T D B p +
    penaltyForm A y + ⟪y,D y⟫_ℝ - 2*⟪y,D z⟫_ℝ at hi
  nlinarith

theorem thirdOrder_rayleigh_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ} (hg : 0 < g)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖) (hD : ‖D‖ ≤ d)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ thirdOrderForm C T D B p)
    (p : L) (q : H) (hpq : 0 < ‖p‖^2+‖q‖^2) :
    μ-(2*d^2/g+2*m)*η^2 ≤ lowBlockRayleigh C A D B p q := by
  have he := thirdOrder_energy_lower C A T D B hg hd hm hsmall hAT hAsymm
    hDsymm hgap hTB hD hμ hmin p q
  unfold lowBlockRayleigh
  apply (le_div_iff₀ hpq).mpr
  have hKq : 0 ≤ (2*d^2/g+2*m)*η^2*‖q‖^2 := by positivity
  nlinarith

theorem thirdOrder_trial_identity (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (hAT : ∀ x, A (T x) = x) (p : L) :
    lowBlockEnergy C A D B p (-(T (B p))) = thirdOrderForm C T D B p := by
  unfold lowBlockEnergy thirdOrderForm effectiveForm
  rw [blockEnergy_trial_identity A T D B hAT]
  simp only [map_neg,inner_neg_left,inner_neg_right]
  ring

theorem thirdOrder_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {m η μ : ℝ} (hm : 0 ≤ m)
    (hAT : ∀ x, A (T x) = x) (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hμ : -m ≤ μ) (p : L) (hp : ‖p‖ = 1) (he : thirdOrderForm C T D B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ+m*η^2 := by
  have hz := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [hp,mul_one] at hz
  unfold lowBlockRayleigh
  rw [thirdOrder_trial_identity C A T D B hAT,he,hp,norm_neg]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1^2+‖T (B p)‖^2)).mpr
  have hmz := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖T (B p)‖)
  have hη := mul_le_mul_of_nonneg_left hz hm
  have hx : 0 ≤ m*η^2*‖T (B p)‖^2 := by positivity
  nlinarith

end ContinuumCoulomb.Perturbation

end

end OAI

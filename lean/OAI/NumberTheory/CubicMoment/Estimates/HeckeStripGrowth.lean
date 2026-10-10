import OAI.NumberTheory.CubicMoment.Estimates.HeckeSmoothDual
import OAI.NumberTheory.CubicMoment.Estimates.PolynomialStrip

namespace OAI

/-! The polynomial strip-growth field used by the Mellin proof follows
from finite order, absolute convergence, and the functional equation.
No polynomial strip bound is assumed in the input structure here. -/

noncomputable section
open Set
namespace CubicFirstMoment

lemma norm_idealDirichlet_le_zeta_two (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤
      ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) := by
  have hb := summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)
  have hf (ν : EisensteinIdealExponent) :
      ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-(2:ℝ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
      (Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (neg_le_neg hs))
  have hfn : Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖) :=
    hb.of_norm_bounded (fun ν => by simpa only [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)] using hf ν)
  exact (norm_tsum_le_tsum_norm hfn).trans (Summable.tsum_le_tsum hf hfn hb)

lemma hecke_left_boundary_bound (χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A : ℝ} (hA : 0 < A)
    {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A 0 ε L Ldual)
    (hd : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    ‖L ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (‖ε‖*A^(2*m)*(3*(m:ℝ)+1)^(2*m)*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))))*(1+|u|)^(2*m) := by
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 2 ≤ (1-s).re := by dsimp [s]; simp; linarith
  have hG : Complex.Gamma (s+(0:ℂ)) ≠ 0 := by
    rw [add_zero]
    exact Complex.Gamma_ne_zero (half_sub_nat_regular m u)
  have hGd : Complex.Gamma (1-s+(0:ℂ)) ≠ 0 := by
    rw [add_zero]
    exact Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have he := hecke_uncompleted hA hFE s hG hGd
  simp only [Complex.ofReal_zero,add_zero] at he
  rw [hd _ (by linarith)] at he
  have hp : ‖(A:ℂ)^(1-2*s)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*s).re = ((2*m:ℕ):ℝ) := by dsimp [s]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hg : ‖Complex.Gamma (1-s)/Complex.Gamma s‖ ≤
      (3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
    have heq : 1-s = (1/2:ℂ)+(m:ℂ)-(u:ℂ)*Complex.I := by dsimp [s]; ring
    rw [heq]
    exact norm_gamma_left_ratio_le m u
  change ‖L s‖ ≤ _
  rw [he,norm_mul,norm_mul,norm_mul,hp]
  calc
    _ ≤ (‖ε‖*A^(2*m))*((3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (norm_idealDirichlet_le_zeta_two χdual hχdual (1-s) hr)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Finite order is the weak growth statement supplied by the classical
completed Hecke-function theory. Its conversion from the completed
order-one bound is kept separate from the Phragmén–Lindelöf argument. -/
structure PrimitiveHeckeFiniteOrderData (χ χdual : EisensteinIdealExponent → ℂ)
    (A : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A 0 ε L Ldual
  finite_order : ∀ m : ℕ, FiniteVerticalOrder L (1/2-(m:ℝ)) 2

/-- Polynomial strip growth follows from finite order and the completed
functional equation, giving the bounds needed for the contour shift. -/
theorem PrimitiveHeckeFiniteOrderData.analyticData
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : PrimitiveHeckeFiniteOrderData χ χdual A ε L Ldual) :
    PrimitiveHeckeAnalyticData χ χdual A ε L Ldual := by
  refine ⟨data.entire,data.right_series,data.dual_right_series,data.functional_equation,?_⟩
  intro m
  let M := m+2
  let a : ℝ := 1/2-(M:ℝ)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let C : ℝ := S+‖ε‖*A^(2*M)*(3*(M:ℝ)+1)^(2*M)*S
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : ∀ z : ℂ, z.re = a → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    have he : z = (1/2:ℂ)-(M:ℂ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [a] at hz ⊢; assumption
    have hb := hecke_left_boundary_bound χdual hχdual hA data.functional_equation
      data.dual_right_series (show 2 ≤ M by dsimp [M]; omega) z.im
    rw [← he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have hb : ∀ z : ℂ, z.re = 2 → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    rw [data.right_series z (by linarith)]
    calc
      _ ≤ S := norm_idealDirichlet_le_zeta_two χ hχ z hz.ge
      _ ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      _ ≤ C*(1+|z.im|)^(2*M) := le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg z.im]))
  have ha2 : a < 2 := by
    dsimp [a]
    have hM : (0:ℝ) ≤ M := by positivity
    linarith
  have hbound := polynomial_strip_of_finite_order
    (a := a) (b := 2) ha2 data.entire (data.finite_order M) hC (2*M) ha hb
  have hapos : 0 < 2-a+1 := by linarith
  refine ⟨C*2^(2*M)*(2-a+1)^(2*M),2*M,by positivity,?_⟩
  intro σ hσ u
  have hσa : a ≤ σ := by
    dsimp [a,M]
    push_cast
    linarith [hσ.1]
  simpa using hbound (σ+(u:ℂ)*Complex.I) (by simpa using And.intro hσa hσ.2)

end CubicFirstMoment

end

end OAI

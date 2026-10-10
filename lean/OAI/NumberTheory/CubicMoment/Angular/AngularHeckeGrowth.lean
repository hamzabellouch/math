import OAI.NumberTheory.CubicMoment.Angular.AngularGamma
import OAI.NumberTheory.CubicMoment.Estimates.HeckeCompletedOrder

namespace OAI

/-! Polynomial strip growth for the shifted completion Gamma(s+k).
The input is the ordinary entire order-one completion, expressed by a
coarse quadratic exponential bound. All strip bounds are derived. -/
noncomputable section
open Set
namespace CubicFirstMoment

def ShiftedCompletedHeckeFiniteOrder (A k : ℝ) (L : ℂ → ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 → Λ s = heckeCompleted A k L s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)

lemma shifted_completed_hecke_decompletion {A k : ℝ} (hA : 0 < A)
    {L Λ : ℂ → ℂ} (hL : Continuous L) (hΛ : Continuous Λ)
    (heq : ∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 → Λ s = heckeCompleted A k L s) :
    L = fun s : ℂ => (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  apply Continuous.ext_on
    ((Set.countable_range (fun n : ℕ => -(n:ℂ)-(k:ℂ))).dense_compl ℂ)
    hL (((differentiable_const_cpow_of_neZero (A:ℂ)).continuous.comp continuous_neg).mul
      (Complex.differentiable_one_div_Gamma.continuous.comp
        (continuous_id.add continuous_const)) |>.mul hΛ)
  intro s hs
  have hG : Complex.Gamma (s+(k:ℂ)) ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    apply hs
    refine ⟨n,?_⟩
    linear_combination -hn)
  change L s = (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s
  rw [heq s hG,heckeCompleted,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  field_simp

theorem shifted_completed_finiteVerticalOrder {A k : ℝ} (hA : 0 < A)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) {a b : ℝ}
    (hGamma : GammaInverseFiniteOrder (a+k) (b+k)) : FiniteVerticalOrder L a b := by
  obtain ⟨Λ,hΛ,heq,C,hC,hbound⟩ := hcomp
  obtain ⟨B,hB,hGamma⟩ := hGamma
  have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
  let R : ℝ := 1+|a|+|b|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a,abs_nonneg b]
  refine ⟨R*|Real.log A|+C*R^2+B,2,by positivity,?_⟩
  intro s hs
  have hreal : |s.re| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hs.1]
    · linarith [le_abs_self b,abs_nonneg a,hs.2]
  have hn : 1+‖s‖ ≤ R*(1+|s.im|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    dsimp [R]
    nlinarith [abs_nonneg a,abs_nonneg b,abs_nonneg s.im]
  have hnsq : (1+‖s‖)^2 ≤ R^2*(1+|s.im|)^2 := by
    calc
      _ ≤ (R*(1+|s.im|))^2 := pow_le_pow_left₀ (by positivity) hn _
      _ = _ := mul_pow _ _ _
  have haexp : ‖(A:ℂ)^(-s)‖ ≤ Real.exp (R*|Real.log A|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA,Complex.neg_re,Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A*(-s.re) ≤ |Real.log A*(-s.re)| := le_abs_self _
      _ = |Real.log A| *|s.re| := by rw [abs_mul,abs_neg]
      _ ≤ |Real.log A| *R := mul_le_mul_of_nonneg_left
        (hreal.trans (by dsimp [R]; linarith)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hg : ‖(Complex.Gamma (s+(k:ℂ)))⁻¹‖ ≤ Real.exp (B*(1+|s.im|)^2) := by
    simpa using hGamma (s+(k:ℂ)) (by simpa using
      (show a+k ≤ s.re+k ∧ s.re+k ≤ b+k from
        ⟨by linarith [hs.1],by linarith [hs.2]⟩))
  have hp : 1 ≤ (1+|s.im|)^2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rw [congrFun hdec s,norm_mul,norm_mul]
  calc
    _ ≤ Real.exp (R*|Real.log A|)*Real.exp (B*(1+|s.im|)^2)*
        Real.exp (C*(1+‖s‖)^2) :=
      mul_le_mul (mul_le_mul haexp hg (_root_.norm_nonneg _) (Real.exp_pos _).le)
        (hbound s) (_root_.norm_nonneg _) (by positivity)
    _ = Real.exp (R*|Real.log A|+B*(1+|s.im|)^2+C*(1+‖s‖)^2) := by
      rw [←Real.exp_add,←Real.exp_add]
    _ ≤ Real.exp ((R*|Real.log A|+C*R^2+B)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ R*|Real.log A| by positivity)
      have h2 := mul_le_mul_of_nonneg_left hnsq hC
      nlinarith

lemma angular_hecke_left_boundary (χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hd : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    ‖L ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (‖ε‖*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))))*(1+|u|)^(2*m) := by
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 2 ≤ (1-s).re := by dsimp [s]; simp; linarith
  have hS : 0 ≤ ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) :=
    tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  by_cases hG : Complex.Gamma (s+(k:ℂ)) = 0
  · obtain ⟨Λ,hΛ,heq,-⟩ := hcomp
    have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
    change ‖L s‖ ≤ _
    rw [congrFun hdec s,hG,inv_zero,mul_zero,zero_mul,norm_zero]
    positivity
  have hGd : Complex.Gamma (1-s+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  have he := hecke_uncompleted hA hFE s hG hGd
  rw [hd _ (by linarith)] at he
  have hp : ‖(A:ℂ)^(1-2*s)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*s).re = ((2*m:ℕ):ℝ) := by dsimp [s]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hg : ‖Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))‖ ≤
      (k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
    have heq : 1-s+(k:ℂ) = (1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    have heq2 : s+(k:ℂ) = (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    rw [heq,heq2]
    exact norm_angular_gamma_left_ratio_le hk m u
  change ‖L s‖ ≤ _
  rw [he,norm_mul,norm_mul,norm_mul,hp]
  calc
    _ ≤ (‖ε‖*A^(2*m))*((k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (norm_idealDirichlet_le_zeta_two χdual hχdual (1-s) hr)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Phragmen--Lindelof derives strip growth for the shifted completion
from its entire order-one bound. -/
structure ShiftedPrimitiveHeckeAnalyticData (χ χdual : EisensteinIdealExponent → ℂ)
    (A k : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A k ε L Ldual
  strip_growth : ∀ m : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧
    ∀ σ ∈ Icc (1/2-(m:ℝ)) 2, ∀ u : ℝ,
      ‖L (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^n

theorem shifted_hecke_analyticData_of_completed
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hGamma : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+k) (2+k)) :
    ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual := by
  refine ⟨hL,hs,hds,hFE,?_⟩
  intro m
  let M := m+2
  let a : ℝ := 1/2-(M:ℝ)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let C : ℝ := S+‖ε‖*A^(2*M)*(k+3*(M:ℝ)+1)^(2*M)*S
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : ∀ z : ℂ, z.re = a → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    have he : z = (1/2:ℂ)-(M:ℂ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [a] at hz ⊢; assumption
    have hb := angular_hecke_left_boundary χdual hχdual hA hk hL hcomp hFE hds
      (show 2 ≤ M by dsimp [M]; omega) z.im
    rw [←he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have hb : ∀ z : ℂ, z.re = 2 → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    rw [hs z (by linarith)]
    calc
      _ ≤ S := norm_idealDirichlet_le_zeta_two χ hχ z hz.ge
      _ ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      _ ≤ C*(1+|z.im|)^(2*M) := le_mul_of_one_le_right hC
        (one_le_pow₀ (by linarith [abs_nonneg z.im]))
  have ha2 : a < 2 := by
    dsimp [a]
    have hM : (0:ℝ) ≤ M := by positivity
    linarith
  have hbound := polynomial_strip_of_finite_order (a := a) (b := 2) ha2 hL
    (shifted_completed_finiteVerticalOrder hA hL hcomp (hGamma M)) hC (2*M) ha hb
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

import OAI.NumberTheory.CubicMoment.Estimates.HeckeStripGrowth
import Mathlib.Topology.Algebra.Module.Cardinality

namespace OAI

/-! Classical order-one completion as the weak analytic input.
Thorner--Zaman, ANT 13 (2019), §2C, p.1049, Eq. (2-15), states
that the completed primitive nonprincipal Hecke function is entire of
order one. The coarse quadratic exponential majorant below is sufficient.
The reciprocal Gamma strip bound is a weak consequence of the uniform
vertical Stirling formula, DLMF 5.11.9, and its entire reciprocal (5.2.2).
These inputs concern individual analytic functions, not arithmetic means. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- An order-one completed function has this deliberately coarse
quadratic exponential bound. The regular-point equality respects Lean's
zero-valued Gamma at its poles. -/
def CompletedHeckeFiniteOrder (A : ℝ) (L : ℂ → ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, Complex.Gamma s ≠ 0 → Λ s = heckeCompleted A 0 L s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)

/-- Weak reciprocal-Gamma growth, on one bounded strip only. -/
def GammaInverseFiniteOrder (a b : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc a b →
    ‖(Complex.Gamma s)⁻¹‖ ≤ Real.exp (B*(1+|s.im|)^2)

lemma completed_hecke_decompletion {A : ℝ} (hA : 0 < A)
    {L Λ : ℂ → ℂ} (hL : Continuous L) (hΛ : Continuous Λ)
    (heq : ∀ s : ℂ, Complex.Gamma s ≠ 0 → Λ s = heckeCompleted A 0 L s) :
    L = fun s : ℂ => (A:ℂ)^(-s)*(Complex.Gamma s)⁻¹*Λ s := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  apply Continuous.ext_on ((Set.countable_range (fun n : ℕ => -(n:ℂ))).dense_compl ℂ)
    hL (((differentiable_const_cpow_of_neZero (A:ℂ)).continuous.comp continuous_neg).mul
      Complex.differentiable_one_div_Gamma.continuous |>.mul hΛ)
  intro s hs
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    exact hs ⟨n,hn.symm⟩)
  change L s = (A:ℂ)^(-s)*(Complex.Gamma s)⁻¹*Λ s
  rw [heq s hG,heckeCompleted,Complex.ofReal_zero,add_zero,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  field_simp

/-- Decompletion preserves finite order. This derives the growth
hypothesis needed for Phragmén–Lindelöf from the published completion. -/
theorem completed_hecke_finiteVerticalOrder {A : ℝ} (hA : 0 < A)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : CompletedHeckeFiniteOrder A L) {a b : ℝ}
    (hGamma : GammaInverseFiniteOrder a b) : FiniteVerticalOrder L a b := by
  obtain ⟨Λ,hΛ,heq,C,hC,hbound⟩ := hcomp
  obtain ⟨B,hB,hGamma⟩ := hGamma
  have hdec := completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
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
      _ ≤ |Real.log A| *R := mul_le_mul_of_nonneg_left (hreal.trans (by dsimp [R]; linarith)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hp : 1 ≤ (1+|s.im|)^2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rw [congrFun hdec s,norm_mul,norm_mul]
  calc
    _ ≤ Real.exp (R*|Real.log A|)*Real.exp (B*(1+|s.im|)^2)*
        Real.exp (C*(1+‖s‖)^2) :=
      mul_le_mul (mul_le_mul haexp (hGamma s hs) (_root_.norm_nonneg _) (Real.exp_pos _).le)
        (hbound s) (_root_.norm_nonneg _) (by positivity)
    _ = Real.exp (R*|Real.log A|+B*(1+|s.im|)^2+C*(1+‖s‖)^2) := by
      rw [← Real.exp_add,← Real.exp_add]
    _ ≤ Real.exp ((R*|Real.log A|+C*R^2+B)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ R*|Real.log A| by positivity)
      have h2 := mul_le_mul_of_nonneg_left hnsq hC
      nlinarith

/-- The completion and reciprocal Gamma bound imply the
polynomial strip bounds for smooth duality. -/
theorem primitiveHeckeAnalyticData_of_completed
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A 0 ε L Ldual)
    (hcomp : CompletedHeckeFiniteOrder A L)
    (hGamma : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2) :
    PrimitiveHeckeAnalyticData χ χdual A ε L Ldual := by
  apply PrimitiveHeckeFiniteOrderData.analyticData hχ hχdual hA
  exact ⟨hL,hs,hds,hFE,fun m => completed_hecke_finiteVerticalOrder hA hL hcomp (hGamma m)⟩

end CubicFirstMoment

end

end OAI

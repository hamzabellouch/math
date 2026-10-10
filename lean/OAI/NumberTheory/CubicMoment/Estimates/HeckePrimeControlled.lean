import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtControlled
import OAI.NumberTheory.CubicMoment.Estimates.HeckeUniformLogDerivative

namespace OAI

/-! A quantitative smooth prime estimate with its explicit finite weight cost deduced from the actual Hecke
functional equations for a character and its square. No prime bound or
zero-free assertion is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem hecke_smooth_prime_bound_controlled :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (W : ℝ → ℂ) (_hW : HasCompactSupport W),
    tsupport W ⊆ Ioi 0 → ContDiff ℝ ∞ W →
    ∀ D : ℝ, PrimeMellinControl W D →
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 u T : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    10 ≤ u → A ≤ u → A2 ≤ u → k+7 ≤ u → k2+7 ≤ u → 4+2*(T+3) ≤ u →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X b : ℝ, 1 ≤ X → 1 < b → b < 1+δ → b ≤ 2 → 0 < T →
      ‖idealMangoldtSmooth χ W X‖ ≤ 6*D*
        (X^(1-heckeZeroFreeWidth u/2)*(heckeLogSquaredConstant*(1+Real.log u)^2)+
          X^b*(heckeLogSquaredConstant*(1+Real.log u)^2+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := idealMangoldt_smooth_bound_controlled
  refine ⟨C,δ,hC,hδ,?_⟩
  intro W hW hpos hsm D hD χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 u T ε ε2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT
    hFE hFE2 hcomp hcomp2 X b hX hb hbδ hb2 hT
  have hw := heckeZeroFreeWidth_pos hu
  have hw1 := heckeZeroFreeWidth_le_one hu
  have ha : 0 ≤ 1-heckeZeroFreeWidth u/2 := by linarith
  have hab : 1-heckeZeroFreeWidth u/2 ≤ b := by linarith
  apply hbound W hW hpos hsm D hD χ hχ hχ0 hχadd L hL hs X (1-heckeZeroFreeWidth u/2) b T
    (heckeLogSquaredConstant*(1+Real.log u)^2) hX ha hab hb hbδ hb2 hT
    (mul_nonneg heckeLogSquaredConstant_pos.le (sq_nonneg _))
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    have him : |s.im| ≤ T := abs_le.mpr hparts.2
    have hheight : 4+|s.im| ≤ u := by linarith
    have hheight2 : 4+|2*s.im| ≤ u := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    rw [←Complex.re_add_im s]
    apply hecke_zero_free_log_from_analytic_pair hχ hχ0 hχadd hχdual hχ2dual hL hL2
      hs hs2 hds hds2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hFE2 hcomp hcomp2
    have hwidth := heckeZeroFreeWidth_le_log hu
    linarith [hparts.1.1]
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    rw [←Complex.re_add_im s]
    exact hecke_logDeriv_norm_uniform_from_analytic_pair hχ hχ0 hχadd hχdual hχ2dual hL hL2
      hs hs2 hds hds2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT hFE hFE2 hcomp hcomp2
      hparts.1.1 (hparts.1.2.trans hb2) (abs_le.mpr hparts.2)

end CubicFirstMoment

end

end OAI

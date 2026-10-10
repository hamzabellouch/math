import OAI.NumberTheory.CubicMoment.Estimates.HeckeCompletedOrder
import OAI.NumberTheory.CubicMoment.Estimates.HeckeTruncatedDual

namespace OAI

/-! Actual smooth Hecke sums are approximated by their retained dual
integrals, with an error smaller than any prescribed power. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def retainedHeckeIntegral (W : ℝ → ℂ) (χdual : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A
        ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

/-- Uniform arbitrary-power approximation beyond the natural dual
length. The original sum and retained integral are explicitly defined. -/
theorem hecke_smooth_approximation
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ χdual : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → (∀ ν, ‖χdual ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J t : ℝ),
      1 ≤ Y → 0 < A → 1 ≤ Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ∀ (L Ldual : ℂ → ℂ), PrimitiveHeckeAnalyticData χ χdual A ε L Ldual →
      GammaQuotientStripBound (1/2-(m:ℝ)) →
      ‖(∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
        retainedHeckeIntegral W χdual ε A Z J t‖ ≤ C*Y^(-R) := by
  obtain ⟨m,C,hm,hC,hbound⟩ := hecke_dual_tail_arbitrary_power W hW hpos hsm hδ B R
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  refine ⟨m,‖c‖*C,hm,mul_nonneg (_root_.norm_nonneg _) hC,?_⟩
  intro χ χdual hχ hχdual ε hε Y A Z J t hY hA hZ hJ hZB hJB hcut L Ldual data hGamma
  have he := hecke_smooth_truncated_identity χ χdual hχ hχdual hA data W hW hpos hsm hZ hm J t hGamma
  have hid : (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
      retainedHeckeIntegral W χdual ε A Z J t =
      c*(∫ τ : ℝ, heckeDualTailIntegrand W χdual ε A Z J m t τ) := by
    dsimp [retainedHeckeIntegral,c]
    linear_combination he
  rw [hid,norm_mul]
  calc
    _ ≤ ‖c‖*(C*Y^(-R)) := mul_le_mul_of_nonneg_left
      (hbound χdual hχdual ε hε Y A Z J hY hA (zero_lt_one.trans_le hZ) hJ hZB hJB t hcut)
      (_root_.norm_nonneg _)
    _ = _ := by ring

/-- Smooth dual approximation from the completed functional equation
and reciprocal-Gamma bounds. -/
theorem hecke_smooth_approximation_of_completed
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ χdual : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → (∀ ν, ‖χdual ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J t : ℝ),
      1 ≤ Y → 0 < A → 1 ≤ Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ∀ (L Ldual : ℂ → ℂ), Differentiable ℂ L →
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s) →
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s) →
      HeckeFunctionalEquation A 0 ε L Ldual → CompletedHeckeFiniteOrder A L →
      (∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2) →
      (∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) →
      ‖(∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
        retainedHeckeIntegral W χdual ε A Z J t‖ ≤ C*Y^(-R) := by
  obtain ⟨m,C,hm,hC,hbound⟩ := hecke_smooth_approximation W hW hpos hsm hδ B R
  refine ⟨C,hC,?_⟩
  intro χ χdual hχ hχdual ε hε Y A Z J t hY hA hZ hJ hZB hJB hcut L Ldual hL hs hds hFE hcomp hGamma hGQ
  exact hbound χ χdual hχ hχdual ε hε Y A Z J t hY hA hZ hJ hZB hJB hcut L Ldual
    (primitiveHeckeAnalyticData_of_completed hχ hχdual hA hL hs hds hFE hcomp hGamma) (hGQ m)

end CubicFirstMoment

end

end OAI

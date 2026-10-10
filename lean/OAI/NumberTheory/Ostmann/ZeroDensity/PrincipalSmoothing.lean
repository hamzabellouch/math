import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingIdentity
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingPNT

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

theorem principal_smoothing_real_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * φ ((n : ℝ)/X)) -
        X * (∫ t in Ioi (0 : ℝ), φ t)| ≤ C*X*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c, K, hc, hK, hPNT⟩ := principal_cumulative_uniform_PNT
  obtain ⟨A, hA⟩ := hcompact.deriv.exists_bound_of_continuous (hφ.continuous_deriv (by simp))
  let M : ℝ := |A| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hderiv (t : ℝ) : ‖deriv φ t‖ ≤ M := by
    exact (hA t).trans (by dsimp [M]; linarith [le_abs_self A])
  refine ⟨c, M*K, hc, mul_pos hM hK, ?_⟩
  filter_upwards [hPNT, eventually_gt_atTop (0 : ℝ)] with X hPX hX
  rw [principal_smoothing_error_identity ArithmeticFunction.vonMangoldt hφ hs hX, abs_neg,
    ← Real.norm_eq_abs]
  have hbound : ‖∫ t in X/2..X,
      (deriv φ (t/X)/X) * (principalCumulative ArithmeticFunction.vonMangoldt t-t)‖ ≤
        (M*K*Real.exp (-c*Real.sqrt (Real.log X))) * |X-X/2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (by linarith : X/2 ≤ X)] at ht
    have herror : ‖principalCumulative ArithmeticFunction.vonMangoldt t-t‖ ≤
        K*X*Real.exp (-c*Real.sqrt (Real.log X)) := by
      simpa only [Real.norm_eq_abs] using hPX t ⟨ht.1.le, ht.2⟩
    rw [norm_mul, norm_div, Real.norm_eq_abs X, abs_of_pos hX]
    calc
      _ ≤ (M/X) * (K*X*Real.exp (-c*Real.sqrt (Real.log X))) :=
        mul_le_mul (div_le_div_of_nonneg_right (hderiv (t/X)) hX.le) herror
          (norm_nonneg _) (div_nonneg hM.le hX.le)
      _ = _ := by field_simp
  calc
    _ ≤ (M*K*Real.exp (-c*Real.sqrt (Real.log X))) * |X-X/2| := hbound
    _ ≤ (M*K*Real.exp (-c*Real.sqrt (Real.log X))) * X := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_of_nonneg (by linarith : 0 ≤ X-X/2)]
      linarith
    _ = _ := by ring

theorem principal_mod_one_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hn, map_one]

theorem smoothError_principal_one_eq (φ : ℝ → ℝ) (X : ℝ) :
    smoothError (1 : DirichletCharacter ℂ 1) φ X =
      (((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * φ ((n : ℝ)/X)) -
        X * (∫ t in Ioi (0 : ℝ), φ t) : ℝ) : ℂ) := by
  classical
  unfold smoothError
  simp only [principal_mod_one_apply, mul_one, ite_true, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, Complex.ofReal_sub]

theorem principal_smoothError_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ‖smoothError (1 : DirichletCharacter ℂ 1) φ X‖ ≤
        C*X*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c, C, hc, hC, h⟩ := principal_smoothing_real_bound hφ hcompact hs
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [h] with X hX
  simpa only [smoothError_principal_one_eq, Complex.norm_real, Real.norm_eq_abs] using hX

end Ostmann.ZeroDensity

end

end OAI

import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! A uniform Mellin bound for functions vanishing on a fixed initial
interval and decaying by a fixed positive power at infinity. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem mellin_cutoff_bound {a b δ ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x : ℝ, 0 < x → x ≤ δ → f x = 0) →
      (∀ x : ℝ, 0 < x → ‖f x‖ ≤ A*x^(-ε)) →
      ∀ s : ℂ, s.re ∈ Icc a b → ‖mellin f (-s)‖ ≤ K*A := by
  let g : ℝ → ℝ := (Ioi δ).indicator (fun x => x^(-a-1-ε)+x^(-b-1-ε))
  have hg : Integrable g := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hδ).add
      (integrableOn_Ioi_rpow_of_lt (by linarith) hδ)
  have hg0 (x : ℝ) : 0 ≤ g x := by
    by_cases hx : x ∈ Ioi δ
    · simp only [g,indicator_of_mem hx]
      exact add_nonneg (Real.rpow_nonneg (hδ.le.trans hx.le) _)
        (Real.rpow_nonneg (hδ.le.trans hx.le) _)
    · simp only [g,indicator_of_notMem hx]; rfl
  refine ⟨∫ x : ℝ in Ioi 0, g x,integral_nonneg hg0,?_⟩
  intro f A hA hzero hbound s hs
  have hpoint (x : ℝ) (hx : x ∈ Ioi 0) :
      ‖(x:ℂ)^(-s-1)*f x‖ ≤ A*g x := by
    by_cases hxd : x ≤ δ
    · rw [hzero x hx hxd,mul_zero,norm_zero]
      exact mul_nonneg hA (hg0 x)
    · have hdx : x ∈ Ioi δ := lt_of_not_ge hxd
      dsimp only [g]
      rw [indicator_of_mem hdx,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hre : (-s-1).re = -s.re-1 := by simp
      rw [hre]
      have hp : x^(-s.re-1) ≤ x^(-a-1)+x^(-b-1) := by
        by_cases hx1 : 1 ≤ x
        · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hs.1])).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
        · exact (Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
            (by linarith [hs.2])).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
      calc
        _ ≤ (x^(-a-1)+x^(-b-1))*(A*x^(-ε)) :=
          mul_le_mul hp (hbound x hx) (_root_.norm_nonneg _)
            (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
        _ = A*(x^(-a-1-ε)+x^(-b-1-ε)) := by
          rw [add_mul]
          have he (c : ℝ) : x^(-c-1)*(A*x^(-ε)) = A*x^(-c-1-ε) := by
            calc
              _ = A*(x^(-c-1)*x^(-ε)) := by ring
              _ = _ := by rw [←Real.rpow_add hx]; congr 1
          rw [he,he,mul_add]
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, A*g x := norm_integral_le_of_norm_le
      (hg.restrict.const_mul A) ((ae_restrict_mem measurableSet_Ioi).mono hpoint)
    _ = _ := by rw [integral_const_mul]; ring

end CubicFirstMoment

end

end OAI

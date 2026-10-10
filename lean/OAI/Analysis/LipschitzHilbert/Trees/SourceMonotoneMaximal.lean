import OAI.Analysis.LipschitzHilbert.Trees.SourceGlobalDyadicMaximal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Passing from finite scale cutoffs to a genuine countable maximal
function. The real-valued representative is defined even on the null set
where the extended supremum is infinite. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

def maximalSquare {X : Type*} (F : ℕ → X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal ((F n x)^2)

def monotoneMaximal {X : Type*} (F : ℕ → X → ℝ) (x : X) : ℝ :=
  Real.sqrt (maximalSquare F x).toReal

theorem maximalSquare_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (maximalSquare F) :=
  Measurable.iSup (fun n => (hF n).pow_const 2 |>.ennreal_ofReal)

theorem monotoneMaximal_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (monotoneMaximal F) :=
  (maximalSquare_measurable F hF).ennreal_toReal.sqrt

/-- A nonnegative increasing sequence with a uniform squared-integral
bound has a measurable L² majorant with the same bound. -/
theorem monotoneMaximal_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ n, Measurable (F n)) (hpos : ∀ n x, 0≤F n x)
    (hmono : Monotone F) (hLp : ∀ n, MemLp (F n) 2 μ)
    (henergy : ∀ n, (∫ x, (F n x)^2 ∂μ)≤C) :
    MemLp (monotoneMaximal F) 2 μ ∧
    (∫ x, (monotoneMaximal F x)^2 ∂μ)≤C ∧
    ∀ᵐ x ∂μ, ∀ n, F n x≤monotoneMaximal F x := by
  have hm := maximalSquare_measurable F hF
  have hlin : (∫⁻ x, maximalSquare F x ∂μ)≤ENNReal.ofReal C := by
    change (∫⁻ x, ⨆ n, ENNReal.ofReal ((F n x)^2) ∂μ)≤ENNReal.ofReal C
    rw [lintegral_iSup]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal (hLp n).integrable_sq
        (Filter.Eventually.of_forall (fun x => sq_nonneg (F n x)))]
      exact ENNReal.ofReal_le_ofReal (henergy n)
    · exact fun n => (hF n).pow_const 2 |>.ennreal_ofReal
    · intro i j hij x
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hpos i x) (hmono hij x) 2)
  have hfin : (∫⁻ x, maximalSquare F x ∂μ)≠∞ :=
    ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top)
  have haefin := ae_lt_top hm hfin
  have hreal := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  have heq : (fun x => (monotoneMaximal F x)^2) =
      (fun x => (maximalSquare F x).toReal) := by
    funext x
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  refine ⟨(memLp_two_iff_integrable_sq
    (monotoneMaximal_measurable F hF).aestronglyMeasurable).mpr
      (heq.symm ▸ hreal),?_,?_⟩
  · rw [heq,integral_toReal hm.aemeasurable haefin]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    simpa only [ENNReal.toReal_ofReal hC] using h
  · filter_upwards [haefin] with x hx
    intro n
    apply Real.le_sqrt_of_sq_le
    have h := ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal ((F n x)^2)) n)
    simpa only [ENNReal.toReal_ofReal (sq_nonneg (F n x))] using h

end LipschitzHilbert

end

end OAI

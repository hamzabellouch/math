import OAI.Analysis.KLS.Convexity.LogConcavity
import OAI.Analysis.KLS.Convexity.PrekopaLeindler
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_space {n : ℕ} {f g h : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have he := PiLp.volume_preserving_toLp (Fin n)
  have hp := AsymptoticStatistics.prekopaLeindler
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    ht0 ht1 (fun x y => hfg (WithLp.toLp 2 x) (WithLp.toLp 2 y))
  simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
    he.lintegral_comp hh] using hp

theorem lintegral_marginal_rpow_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (f : E → Space n → ℝ≥0∞) (hf : ∀ u, Measurable (f u))
    (hjoint : ∀ u v x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y))
    (u v : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ x, f u x) ^ t * (∫⁻ y, f v y) ^ (1 - t) ≤
      ∫⁻ z, f (t • u + (1 - t) • v) z :=
  prekopaLeindler_space (hf u) (hf v) (hf _) ht0 ht1
    (fun x y => hjoint u v x y t ht0 ht1)

theorem isLogConcaveFunction_marginal {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (f : E → Space n → ℝ≥0∞) (hf : ∀ u, Measurable (f u))
    (hfinite : ∀ u, (∫⁻ x, f u x) ≠ ⊤)
    (hjoint : ∀ u v x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y)) :
    IsLogConcaveFunction (fun u => (∫⁻ x, f u x).toReal) := by
  apply isLogConcaveFunction_of_ennreal hfinite
  exact fun u v t ht0 ht1 => lintegral_marginal_rpow_le f hf hjoint u v ht0 ht1

def linearSurvival {n : ℕ} (ρ : Space n → ℝ) (L : Space n →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  (densityMeasure ρ {x | t ≤ L x}).toReal

def coordinateSurvival {n : ℕ} (ρ : Space n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  (densityMeasure ρ {x | t ≤ x i}).toReal

theorem measurableSet_linear_superlevel {n : ℕ} (L : Space n →L[ℝ] ℝ) (t : ℝ) :
    MeasurableSet {x | t ≤ L x} :=
  (isClosed_le continuous_const L.continuous).measurableSet

theorem linearSurvival_isLogConcaveFunction {n : ℕ} {ρ : Space n → ℝ}
    (hρ : IsLogConcaveDensity ρ) (L : Space n →L[ℝ] ℝ) :
    IsLogConcaveFunction (linearSurvival ρ L) := by
  let : IsProbabilityMeasure (densityMeasure ρ) := hρ.probability
  let f : ℝ → Space n → ℝ≥0∞ := fun t =>
    {x | t ≤ L x}.indicator (fun x => ENNReal.ofReal (ρ x))
  have hf (t : ℝ) : Measurable (f t) :=
    hρ.measurable.ennreal_ofReal.indicator (measurableSet_linear_superlevel L t)
  have hmass (t : ℝ) : (densityMeasure ρ) {x | t ≤ L x} = ∫⁻ x, f t x := by
    rw [densityMeasure, withDensity_apply _ (measurableSet_linear_superlevel L t)]
    exact (lintegral_indicator (measurableSet_linear_superlevel L t) _).symm
  have hfinite (t : ℝ) : (∫⁻ x, f t x) ≠ ⊤ := by
    rw [← hmass]
    exact measure_ne_top _ _
  have hjoint : ∀ u v x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y) := by
    intro u v x y t ht0 ht1
    by_cases hx : u ≤ L x
    · by_cases hy : v ≤ L y
      · have hz : t • u + (1 - t) • v ≤ L (t • x + (1 - t) • y) := by
          simp only [map_add, map_smul, smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hx ht0.le)
            (mul_le_mul_of_nonneg_left hy (sub_pos.mpr ht1).le)
        simpa only [f, Set.indicator, mem_ofPred_eq, ite_eq_left hx, ite_eq_left hy,
          ite_eq_left hz] using
          hρ.isLogConcaveFunction.ennreal_rpow_le x y ht0 ht1
      · simp only [f, Set.indicator, mem_ofPred_eq, ite_eq_right hy, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1),
          mul_zero, zero_le]
    · simp only [f, Set.indicator, mem_ofPred_eq, ite_eq_right hx, ENNReal.zero_rpow_of_pos ht0, zero_mul, zero_le]
  have h := isLogConcaveFunction_marginal f hf hfinite hjoint
  have heq : linearSurvival ρ L = fun t => (∫⁻ x, f t x).toReal := by
    funext t
    exact congrArg ENNReal.toReal (hmass t)
  rw [heq]
  exact h

theorem linearSurvival_log_concave {n : ℕ} {ρ : Space n → ℝ}
    (hρ : IsLogConcaveDensity ρ) (L : Space n →L[ℝ] ℝ) :
    ConcaveOn ℝ {t | 0 < linearSurvival ρ L t}
      (fun t => Real.log (linearSurvival ρ L t)) :=
  (linearSurvival_isLogConcaveFunction hρ L).log_concave

theorem coordinateSurvival_log_concave {n : ℕ} {ρ : Space n → ℝ}
    (hρ : IsLogConcaveDensity ρ) (i : Fin n) :
    ConcaveOn ℝ {t | 0 < coordinateSurvival ρ i t}
      (fun t => Real.log (coordinateSurvival ρ i t)) :=
  linearSurvival_log_concave hρ (PiLp.proj 2 (fun _ : Fin n => ℝ) i)

end LeanBlast.KLS

end

end OAI

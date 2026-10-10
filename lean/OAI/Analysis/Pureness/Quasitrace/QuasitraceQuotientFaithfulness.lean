import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientCStar

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_zero : T.quotientValue hadd hsqrt 0 = 0 := by
  have h := T.quotientValue_embedding hadd hsqrt (0 : D)
  rw [_root_.map_zero] at h
  exact h.trans (by
    have hz := T.complexValue_positive (Positive.zero : Positive D)
    rw [T.map_zero,Complex.ofReal_zero] at hz
    exact hz)

lemma quotientValue_square_eq_zero_iff (x : T.CauchyQuotient hadd) :
    T.quotientValue hadd hsqrt (star x*x) = 0 ↔ x = 0 := by
  constructor
  · obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
    intro hz
    rw [← T.cauchyQuotientMap_star,← map_mul,T.quotientValue_map] at hz
    have ht := (Complex.continuous_re.tendsto _).comp (T.cauchyValue_tendsto hadd hsqrt (star u*u))
    rw [hz] at ht
    have he (k : ℕ) : (T.complexValue ((star u*u).1 k)).re = T (Positive.starMul (u.1 k)) := by
      change (T.complexValue (Positive.starMul (u.1 k)).1).re = _
      rw [T.complexValue_positive,Complex.ofReal_re]
    simp only [Function.comp_def,he,Complex.zero_re] at ht
    have hn : T.IsMetricNull (fun k => u.1 k) := by
      have hc := (Real.continuous_rpow_const (show 0 ≤ (3:ℝ)⁻¹ by positivity)).tendsto (0 : ℝ)
      have hh := hc.comp ht
      simpa only [IsMetricNull,metricSize,Function.comp_def,Real.zero_rpow (show (3:ℝ)⁻¹ ≠ 0 by norm_num)] using hh
    apply Quotient.sound
    change u ∈ T.nullSequenceIdeal hadd
    rw [nullSequenceIdeal_mem]
    exact hn
  · rintro rfl
    simpa using T.quotientValue_zero hadd hsqrt
end CuntzPureness.PositiveQuasitrace

end

end OAI

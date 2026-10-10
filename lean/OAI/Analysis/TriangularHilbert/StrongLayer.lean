import OAI.Analysis.TriangularHilbert.IntWeak

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def squareLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun t => t^2) t

def oneLayer (a t : ℝ) : ℝ := (Set.Ioo 0 (Real.sqrt a)).indicator (fun _ => (1:ℝ)) t

lemma squareLayer_integrable (a : ℝ) : Integrable (squareLayer a) := by
  have h : IntegrableOn (fun t : ℝ => t^2) (Set.Icc 0 (Real.sqrt a)) volume :=
    (continuous_id.pow 2).integrableOn_Icc
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (h.mono_set Set.Ioo_subset_Icc_self)

lemma oneLayer_integrable (a : ℝ) : Integrable (oneLayer a) := by
  have h : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioo 0 (Real.sqrt a)) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact (integrable_indicator_iff measurableSet_Ioo).mpr h

lemma integral_squareLayer {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, squareLayer a t) = a * Real.sqrt a / 3 := by
  simp only [squareLayer]
  rw [integral_indicator measurableSet_Ioo]
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (Real.sqrt_nonneg a)]
  rw [integral_pow]
  have he : (Real.sqrt a)^3 = a*Real.sqrt a := by
    rw [pow_succ,Real.sq_sqrt ha]
  norm_num [he]

lemma integral_oneLayer (a : ℝ) : (∫ t, oneLayer a t) = Real.sqrt a := by
  simp only [oneLayer]
  rw [integral_indicator measurableSet_Ioo,← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (Real.sqrt_nonneg a),intervalIntegral.integral_const]
  simp

lemma layer_iff {a t : ℝ} (ht : 0 < t) :
    t ∈ Set.Ioo 0 (Real.sqrt a) ↔ t^2 < a := by
  exact and_iff_right ht |>.trans (Real.lt_sqrt (by positivity))

end
end TriangularHilbert
end

end OAI

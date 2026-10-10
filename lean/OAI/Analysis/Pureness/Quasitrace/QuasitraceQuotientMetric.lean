import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFaithfulness

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def quotientMetricSize (x : T.CauchyQuotient hadd) : ℝ :=
  (T.quotientValue hadd hsqrt (star x*x)).re ^ ((3:ℝ)⁻¹)

lemma quotientMetricSize_nonneg (x : T.CauchyQuotient hadd) : 0 ≤ T.quotientMetricSize hadd hsqrt x :=
  Real.rpow_nonneg (Complex.nonneg_iff.mp (T.quotientValue_square_nonneg hadd hsqrt x)).1 _

lemma quotientMetricSize_cube (x : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt x ^ 3 = (T.quotientValue hadd hsqrt (star x*x)).re :=
  Real.rpow_inv_natCast_pow (Complex.nonneg_iff.mp (T.quotientValue_square_nonneg hadd hsqrt x)).1 (by norm_num)

lemma quotientMetricSize_zero : T.quotientMetricSize hadd hsqrt 0 = 0 := by
  simp only [quotientMetricSize,star_zero,mul_zero,T.quotientValue_zero,Complex.zero_re,
    Real.zero_rpow (show (3:ℝ)⁻¹ ≠ 0 by norm_num)]

lemma quotientMetricSize_eq_zero_iff (x : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (T.quotientValue_square_eq_zero_iff hadd hsqrt x).mp
    apply Complex.ext
    · have hc := T.quotientMetricSize_cube hadd hsqrt x
      rw [h,zero_pow (by decide : 3 ≠ 0)] at hc
      exact hc.symm
    · exact (Complex.nonneg_iff.mp (T.quotientValue_square_nonneg hadd hsqrt x)).2.symm
  · rintro rfl; exact T.quotientMetricSize_zero hadd hsqrt

lemma quotientMetricSize_neg (x : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt (-x) = T.quotientMetricSize hadd hsqrt x := by
  simp only [quotientMetricSize,star_neg,neg_mul_neg]

lemma quotientMetricSize_star (x : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt (star x) = T.quotientMetricSize hadd hsqrt x := by
  simp only [quotientMetricSize,star_star,← T.quotientValue_polar hadd hsqrt x]

lemma quotientMetricSize_map_tendsto (u : T.cauchySequenceAlgebra hadd) :
    Tendsto (fun k => T.metricSize (u.1 k)) atTop
      (nhds (T.quotientMetricSize hadd hsqrt (T.cauchyQuotientMap hadd u))) := by
  have ht := (Complex.continuous_re.tendsto _).comp (T.cauchyValue_tendsto hadd hsqrt (star u*u))
  have he (k : ℕ) : (T.complexValue ((star u*u).1 k)).re = T (Positive.starMul (u.1 k)) := by
    change (T.complexValue (Positive.starMul (u.1 k)).1).re = _
    rw [T.complexValue_positive,Complex.ofReal_re]
  simp only [Function.comp_def,he] at ht
  have hc := (Real.continuous_rpow_const (show 0 ≤ (3:ℝ)⁻¹ by positivity)).tendsto (T.cauchyValue hadd hsqrt (star u*u)).re
  have hh := hc.comp ht
  rw [quotientMetricSize,← T.cauchyQuotientMap_star,← map_mul,T.quotientValue_map]
  exact hh

lemma quotientMetricSize_add (x y : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt (x+y) ≤
      T.quotientMetricSize hadd hsqrt x+T.quotientMetricSize hadd hsqrt y := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective hadd y
  rw [← map_add]
  exact le_of_tendsto_of_tendsto (T.quotientMetricSize_map_tendsto hadd hsqrt (u+v))
    ((T.quotientMetricSize_map_tendsto hadd hsqrt u).add (T.quotientMetricSize_map_tendsto hadd hsqrt v))
    (Eventually.of_forall (fun k => hadd (u.1 k) (v.1 k)))

lemma quotientMetricSize_embedding (x : D) :
    T.quotientMetricSize hadd hsqrt (T.quotientEmbedding hadd x) = T.metricSize x := by
  exact tendsto_nhds_unique (T.quotientMetricSize_map_tendsto hadd hsqrt (T.constantCauchy hadd x)) tendsto_const_nhds

def quotientDistance (x y : T.CauchyQuotient hadd) : ℝ := T.quotientMetricSize hadd hsqrt (x-y)
lemma quotientDistance_nonneg (x y : T.CauchyQuotient hadd) : 0 ≤ T.quotientDistance hadd hsqrt x y :=
  T.quotientMetricSize_nonneg hadd hsqrt _
lemma quotientDistance_self (x : T.CauchyQuotient hadd) : T.quotientDistance hadd hsqrt x x = 0 := by
  rw [quotientDistance,sub_self,T.quotientMetricSize_zero]
lemma quotientDistance_comm (x y : T.CauchyQuotient hadd) :
    T.quotientDistance hadd hsqrt x y = T.quotientDistance hadd hsqrt y x := by
  rw [quotientDistance,quotientDistance,← neg_sub x y,T.quotientMetricSize_neg]
lemma quotientDistance_triangle (x y z : T.CauchyQuotient hadd) :
    T.quotientDistance hadd hsqrt x z ≤ T.quotientDistance hadd hsqrt x y+T.quotientDistance hadd hsqrt y z := by
  simpa only [quotientDistance,sub_add_sub_cancel] using T.quotientMetricSize_add hadd hsqrt (x-y) (y-z)
lemma quotientDistance_eq_zero_iff (x y : T.CauchyQuotient hadd) :
    T.quotientDistance hadd hsqrt x y = 0 ↔ x = y := by
  rw [quotientDistance,T.quotientMetricSize_eq_zero_iff,sub_eq_zero]

@[instance_reducible]
def quotientMetricSpace : MetricSpace (T.CauchyQuotient hadd) where
  dist := T.quotientDistance hadd hsqrt
  dist_self := T.quotientDistance_self hadd hsqrt
  dist_comm := T.quotientDistance_comm hadd hsqrt
  dist_triangle := T.quotientDistance_triangle hadd hsqrt
  eq_of_dist_eq_zero := fun h => (T.quotientDistance_eq_zero_iff hadd hsqrt _ _).mp h

lemma quotientDistance_embedding (x y : D) :
    T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd x) (T.quotientEmbedding hadd y) = T.distance x y := by
  rw [quotientDistance,← map_sub,T.quotientMetricSize_embedding,distance]

lemma quotientDistance_map_tendsto (u v : T.cauchySequenceAlgebra hadd) :
    Tendsto (fun k => T.distance (u.1 k) (v.1 k)) atTop
      (nhds (T.quotientDistance hadd hsqrt (T.cauchyQuotientMap hadd u) (T.cauchyQuotientMap hadd v))) := by
  rw [quotientDistance,← map_sub]
  exact T.quotientMetricSize_map_tendsto hadd hsqrt (u-v)
end CuntzPureness.PositiveQuasitrace

end

end OAI

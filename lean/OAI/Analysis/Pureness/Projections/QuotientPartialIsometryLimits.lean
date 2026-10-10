import OAI.Analysis.Pureness.Projections.PartialIsometryExtension
import OAI.Analysis.Pureness.Projections.QuotientProjectionLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

theorem quotient_partial_isometry_extension_distance
    (u v : T.CauchyQuotient hadd)
    (hu : IsStarProjection (star u*u)) (hv : IsStarProjection (star v*v))
    (hle : star u*u ≤ star v*v) (hext : v*(star u*u)=u) :
    T.quotientDistance hadd hsqrt v u =
      T.quotientDistance hadd hsqrt (star v*v) (star u*u) := by
  apply (pow_left_inj₀ (T.quotientDistance_nonneg hadd hsqrt _ _)
    (T.quotientDistance_nonneg hadd hsqrt _ _) (by decide : 3 ≠ 0)).mp
  have hd := (hu.le_iff_sub hv).mp hle
  simp only [quotientDistance, T.quotientMetricSize_cube,
    partial_isometry_extension_square u v hu hv hle hext,
    hd.isSelfAdjoint.star_eq, hd.isIdempotentElem.eq]

theorem quotient_compatible_partial_isometries_metricCauchy
    (v : ℕ → T.CauchyQuotient hadd) (hv : ∀ n, IsStarProjection (star (v n)*v n))
    (hm : Monotone (fun n => star (v n)*v n))
    (he : ∀ m n, m ≤ n → v n*(star (v m)*v m)=v m) :
    T.QuotientIsMetricCauchy hadd hsqrt v := by
  have hdist (m n : ℕ) : T.quotientDistance hadd hsqrt (v m) (v n) =
      T.quotientDistance hadd hsqrt (star (v m)*v m) (star (v n)*v n) := by
    rcases le_total m n with h | h
    · rw [T.quotientDistance_comm hadd hsqrt (v m),
        T.quotientDistance_comm hadd hsqrt (star (v m)*v m)]
      exact T.quotient_partial_isometry_extension_distance hadd hsqrt _ _ (hv m) (hv n) (hm h) (he m n h)
    · exact T.quotient_partial_isometry_extension_distance hadd hsqrt _ _ (hv n) (hv m) (hm h) (he n m h)
  simpa only [QuotientIsMetricCauchy,hdist] using
    T.quotient_projections_metricCauchy hadd hsqrt (fun n => star (v n)*v n) hv hm

theorem exists_quotient_compatible_partial_isometry_limit
    (v : ℕ → T.CauchyQuotient hadd) (hv : ∀ n, IsStarProjection (star (v n)*v n))
    (hm : Monotone (fun n => star (v n)*v n))
    (he : ∀ m n, m ≤ n → v n*(star (v m)*v m)=v m) :
    ∃ w : T.CauchyQuotient hadd, IsStarProjection (star w*w) ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (v n) w) atTop (nhds 0) ∧
      (∀ n, w*(star (v n)*v n)=v n) ∧
      (∀ n, star (v n)*v n ≤ star w*w) := by
  have hb (n : ℕ) : ‖v n‖ ≤ 1 := partial_isometry_norm_le_one _ (hv n)
  obtain ⟨w,hw,hl⟩ := T.quotient_bounded_metric_limit hadd hsqrt v
    (T.quotient_compatible_partial_isometries_metricCauchy hadd hsqrt v hv hm he) 1 zero_le_one hb
  have hs := T.quotient_metric_limit_star hadd hsqrt hl
  have hsq := T.quotient_metric_limit_mul hadd hsqrt hs hl 1 zero_le_one
    (fun n => by simpa only [norm_star] using hb n)
  have hp := T.quotient_projection_metric_limit hadd hsqrt hv hsq
  have hc (a : T.CauchyQuotient hadd) :
      Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt a a) atTop (nhds 0) := by
    simp only [T.quotientDistance_self]
    exact tendsto_const_nhds
  have hext (m : ℕ) : w*(star (v m)*v m)=v m := by
    have hlm := T.quotient_metric_limit_mul hadd hsqrt hl (hc (star (v m)*v m)) 1 zero_le_one hb
    have hconst : Tendsto (fun n => T.quotientDistance hadd hsqrt (v n*(star (v m)*v m)) (v m))
        atTop (nhds 0) := by
      apply (hc (v m)).congr'
      filter_upwards [eventually_ge_atTop m] with n hn
      rw [he m n hn]
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ hlm hconst
  refine ⟨w,hp,hl,hext,?_⟩
  intro m
  apply ((hv m).le_iff_mul_eq_right hp).mpr
  have hmul := T.quotient_metric_limit_mul hadd hsqrt hsq (hc (star (v m)*v m))
    1 zero_le_one (fun n => T.quotient_projection_norm_le_one hadd (hv n))
  have hconst : Tendsto (fun n => T.quotientDistance hadd hsqrt
      ((star (v n)*v n)*(star (v m)*v m)) (star (v m)*v m)) atTop (nhds 0) := by
    apply (hc (star (v m)*v m)).congr'
    filter_upwards [eventually_ge_atTop m] with n hn
    rw [((hv m).le_iff_mul_eq_right (hv n)).mp (hm hn)]
  exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ hmul hconst
end CuntzPureness.PositiveQuasitrace

end

end OAI

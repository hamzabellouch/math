import OAI.Analysis.Pureness.States.QuotientGenuineQuasitrace
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientValueMetricLimits
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_projection_norm_le_one {p : T.CauchyQuotient hadd} (hp : IsStarProjection p) :
    ‖p‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg p hp.nonneg).mpr (sub_nonneg.mp hp.one_sub.nonneg)

lemma quotientValue_sub_commute (x y : selfAdjoint (T.CauchyQuotient hadd)) (h : Commute x.1 y.1) :
    T.quotientValue hadd hsqrt (x.1-y.1) =
      T.quotientValue hadd hsqrt x.1-T.quotientValue hadd hsqrt y.1 := by
  simpa only [sub_eq_add_neg, T.quotientValue_neg] using
    T.quotientValue_add_commute hadd hsqrt x ⟨-y.1,y.2.neg⟩ h.neg_right

lemma quotient_projections_metricCauchy (u : ℕ → T.CauchyQuotient hadd)
    (hu : ∀ n, IsStarProjection (u n)) (hmono : Monotone u) :
    T.QuotientIsMetricCauchy hadd hsqrt u := by
  let v (n : ℕ) := (T.quotientValue hadd hsqrt (u n)).re
  have hv : Monotone v := fun m n hmn => (Complex.le_def.mp
    (T.quotientValue_positive_mono hadd hsqrt
      (x := ⟨u m,(hu m).nonneg⟩) (y := ⟨u n,(hu n).nonneg⟩) (hmono hmn))).1
  have hvb : BddAbove (Set.range v) := by
    refine ⟨(T.quotientValue hadd hsqrt 1).re,?_⟩
    rintro _ ⟨n,rfl⟩
    exact (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt
      (x := ⟨u n,(hu n).nonneg⟩) (y := ⟨1,zero_le_one⟩)
      (show u n ≤ 1 from sub_nonneg.mp (hu n).one_sub.nonneg))).1
  have hvC : CauchySeq v := (tendsto_atTop_ciSup hv hvb).cauchySeq
  have hforward (m n : ℕ) (hmn : m ≤ n) :
      T.quotientDistance hadd hsqrt (u m) (u n) ^ 3 ≤ |v m-v n| := by
    let z : Positive (T.CauchyQuotient hadd) := ⟨u n-u m,sub_nonneg.mpr (hmono hmn)⟩
    have hz1 : z.1 ≤ 1 := (sub_le_self _ (hu m).nonneg).trans
      (sub_nonneg.mp (hu n).one_sub.nonneg)
    have h := T.quotientMetricSize_positive_cube_le hadd hsqrt z hz1
    have he := congrArg Complex.re (T.quotientValue_sub_commute hadd hsqrt
      ⟨u n,(hu n).isSelfAdjoint⟩ ⟨u m,(hu m).isSelfAdjoint⟩
      ((hu m).commute_of_le (hu n) (hmono hmn)).symm)
    change (T.quotientValue hadd hsqrt z.1).re = _ at he
    rw [Complex.sub_re] at he
    rw [he] at h
    rw [T.quotientDistance_comm hadd hsqrt (u m) (u n)]
    change T.quotientMetricSize hadd hsqrt z.1 ^ 3 ≤ |v m-v n|
    exact h.trans (by dsimp [v]; exact (le_abs_self _).trans_eq (abs_sub_comm _ _))
  have hbound (m n : ℕ) : T.quotientDistance hadd hsqrt (u m) (u n) ^ 3 ≤ |v m-v n| := by
    rcases le_total m n with h | h
    · exact hforward m n h
    · have he := hforward n m h
      rwa [T.quotientDistance_comm hadd hsqrt (u n) (u m),abs_sub_comm (v n) (v m)] at he
  have hv0 := (cauchySeq_iff_tendsto_dist_atTop_0).mp hvC
  rw [QuotientIsMetricCauchy,Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hv0) (ε^3) (pow_pos hε _)
  filter_upwards [he] with p hp
  have hp' : |v p.1-v p.2| < ε^3 := by
    simpa only [Real.dist_eq,sub_zero,abs_abs] using hp
  have hd : T.quotientDistance hadd hsqrt (u p.1) (u p.2) < ε :=
    (pow_lt_pow_iff_left₀ (T.quotientDistance_nonneg hadd hsqrt _ _) hε.le (by decide : 3 ≠ 0)).mp
      ((hbound p.1 p.2).trans_lt hp')
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] using hd

lemma quotient_projection_metric_limit {u : ℕ → T.CauchyQuotient hadd} {p : T.CauchyQuotient hadd}
    (hu : ∀ n, IsStarProjection (u n))
    (hp : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) p) atTop (nhds 0)) :
    IsStarProjection p := by
  have hsa := T.quotient_metric_limit_selfAdjoint hadd hsqrt hp (fun n => (hu n).isSelfAdjoint)
  have hmul := T.quotient_metric_limit_mul hadd hsqrt hp hp 1 zero_le_one
    (fun n => T.quotient_projection_norm_le_one hadd (hu n))
  simp only [(hu _).isIdempotentElem.eq] at hmul
  exact ⟨T.quotient_metric_limit_unique hadd hsqrt u (p*p) p hmul hp,hsa⟩

lemma exists_quotient_projection_sup (u : ℕ → T.CauchyQuotient hadd)
    (hu : ∀ n, IsStarProjection (u n)) (hmono : Monotone u) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) p) atTop (nhds 0) ∧
      (∀ n, u n ≤ p) ∧ (∀ q, IsStarProjection q → (∀ n, u n ≤ q) → p ≤ q) := by
  have hb (n : ℕ) := T.quotient_projection_norm_le_one hadd (hu n)
  obtain ⟨p,_,hp⟩ := T.quotient_bounded_metric_limit hadd hsqrt u
    (T.quotient_projections_metricCauchy hadd hsqrt u hu hmono) 1 zero_le_one hb
  have hproj := T.quotient_projection_metric_limit hadd hsqrt hu hp
  have hc (q : T.CauchyQuotient hadd) :
      Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt q q) atTop (nhds 0) := by
    simp only [T.quotientDistance_self]; exact tendsto_const_nhds
  refine ⟨p,hproj,hp,?_,?_⟩
  · intro m
    apply ((hu m).le_iff_mul_eq_right hproj).mpr
    have ht := T.quotient_metric_limit_mul hadd hsqrt hp (hc (u m)) 1 zero_le_one hb
    have he : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n*u m) (u m)) atTop (nhds 0) := by
      apply (hc (u m)).congr'
      filter_upwards [eventually_ge_atTop m] with n hn
      rw [((hu m).le_iff_mul_eq_right (hu n)).mp (hmono hn)]
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ ht he
  · intro q hq hle
    apply (hproj.le_iff_mul_eq_left hq).mpr
    have ht := T.quotient_metric_limit_mul hadd hsqrt hp (hc q) 1 zero_le_one hb
    simp only [((hu _).le_iff_mul_eq_left hq).mp (hle _)] at ht
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ ht hp
end CuntzPureness.PositiveQuasitrace

end

end OAI

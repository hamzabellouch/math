import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetricOperations
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientBoundedLimits
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_neg (x : T.CauchyQuotient hadd) :
    T.quotientValue hadd hsqrt (-x) = -T.quotientValue hadd hsqrt x := by
  have h := T.quotientValue_real_smul hadd hsqrt (-1) x
  calc
    _ = T.quotientValue hadd hsqrt ((-1 : ℝ) • x) :=
      congrArg (T.quotientValue hadd hsqrt) (neg_one_smul ℝ x).symm
    _ = _ := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using h

lemma quotientValue_cfc_sub (x : selfAdjoint (T.CauchyQuotient hadd))
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    T.quotientValue hadd hsqrt (cfc f x.1-cfc g x.1) =
      T.quotientValue hadd hsqrt (cfc f x.1)-T.quotientValue hadd hsqrt (cfc g x.1) := by
  have h := T.quotientValue_cfc_add hadd hsqrt x f (fun t => -g t) hf hg.neg
  have he : cfc (fun t => -g t) x.1 = -cfc g x.1 := cfc_neg g x.1
  rw [he,T.quotientValue_neg] at h
  simpa only [sub_eq_add_neg] using h

lemma quotientMetricSize_positive_cube_le (x : Positive (T.CauchyQuotient hadd)) (hx : x.1 ≤ 1) :
    T.quotientMetricSize hadd hsqrt x.1 ^ 3 ≤ (T.quotientValue hadd hsqrt x.1).re := by
  have hc : Commute x.1 (1-x.1) := (Commute.one_right _).sub_right (Commute.refl _)
  have hp := Commute.mul_nonneg x.2 (sub_nonneg.mpr hx) hc
  rw [mul_sub,mul_one] at hp
  have hsq : Positive.starMul x.1 ≤ x := by
    change star x.1*x.1 ≤ x.1
    rw [x.2.isSelfAdjoint.star_eq]
    exact sub_nonneg.mp hp
  rw [T.quotientMetricSize_cube]
  exact (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt hsq)).1

lemma quotient_root_eq_cfc (x : Positive (T.CauchyQuotient hadd)) (n : ℕ) :
    (Positive.power (Positive.rootExponent n) x).1 = cfc (fun t : ℝ => t^(Positive.rootExponent n : ℝ)) x.1 := by
  change CFC.nnrpow x.1 (Positive.rootExponent n) = _
  have hf0 : (fun t : ℝ => t^(Positive.rootExponent n : ℝ)) 0 = 0 := by
    apply Real.zero_rpow
    exact_mod_cast (Positive.rootExponent_pos n).ne'
  rw [CFC.nnrpow_eq_pow,CFC.nnrpow_eq_cfcₙ_real x.1 _ x.2,cfcₙ_eq_cfc (hf0 := hf0)]

lemma quotient_root_value_sub (x : Positive (T.CauchyQuotient hadd)) (m n : ℕ) :
    T.quotientValue hadd hsqrt ((Positive.power (Positive.rootExponent m) x).1-
      (Positive.power (Positive.rootExponent n) x).1) =
    T.quotientValue hadd hsqrt (Positive.power (Positive.rootExponent m) x).1-
      T.quotientValue hadd hsqrt (Positive.power (Positive.rootExponent n) x).1 := by
  rw [T.quotient_root_eq_cfc hadd x m,T.quotient_root_eq_cfc hadd x n]
  exact T.quotientValue_cfc_sub hadd hsqrt ⟨x.1,x.2.isSelfAdjoint⟩ _ _
    (Real.continuous_rpow_const (Positive.rootExponent m).2)
    (Real.continuous_rpow_const (Positive.rootExponent n).2)

lemma quotient_roots_metricCauchy (x : Positive (T.CauchyQuotient hadd)) (hx : ‖x.1‖ ≤ 1) :
    T.QuotientIsMetricCauchy hadd hsqrt (fun n => (Positive.power (Positive.rootExponent n) x).1) := by
  let a (n : ℕ) := Positive.power (Positive.rootExponent n) x
  let v (n : ℕ) := (T.quotientValue hadd hsqrt (a n).1).re
  have ha := Positive.roots_monotone x hx
  have hb (n : ℕ) : (a n).1 ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (a n).2).mp
      (Positive.power_norm_le_one _ (Positive.rootExponent_pos n) x hx)
  have hv : Monotone v := fun m n hmn => (Complex.le_def.mp
    (T.quotientValue_positive_mono hadd hsqrt (ha hmn))).1
  have hvb : BddAbove (Set.range v) := by
    refine ⟨(T.quotientValue hadd hsqrt 1).re,?_⟩
    rintro _ ⟨n,rfl⟩
    exact (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt
      (x := a n) (y := ⟨1,zero_le_one⟩) (hb n))).1
  have hvC : CauchySeq v := (tendsto_atTop_ciSup hv hvb).cauchySeq
  have hforward (m n : ℕ) (hmn : m ≤ n) :
      T.quotientDistance hadd hsqrt (a m).1 (a n).1 ^ 3 ≤ |v m-v n| := by
    let z : Positive (T.CauchyQuotient hadd) := ⟨(a n).1-(a m).1,sub_nonneg.mpr (ha hmn)⟩
    have hz1 : z.1 ≤ 1 := (sub_le_self _ (a m).2).trans (hb n)
    have h := T.quotientMetricSize_positive_cube_le hadd hsqrt z hz1
    have he := congrArg Complex.re (T.quotient_root_value_sub hadd hsqrt x n m)
    change (T.quotientValue hadd hsqrt z.1).re = (T.quotientValue hadd hsqrt (a n).1-
      T.quotientValue hadd hsqrt (a m).1).re at he
    rw [Complex.sub_re] at he
    rw [he] at h
    rw [T.quotientDistance_comm hadd hsqrt (a m).1 (a n).1]
    change T.quotientMetricSize hadd hsqrt z.1 ^ 3 ≤ |v m-v n|
    exact h.trans (by dsimp [v]; exact le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
  have hbound (m n : ℕ) : T.quotientDistance hadd hsqrt (a m).1 (a n).1 ^ 3 ≤ |v m-v n| := by
    rcases le_total m n with h | h
    · exact hforward m n h
    · have he := hforward n m h
      rwa [T.quotientDistance_comm hadd hsqrt (a n).1 (a m).1,abs_sub_comm (v n) (v m)] at he
  have hv0 := (cauchySeq_iff_tendsto_dist_atTop_0).mp hvC
  rw [QuotientIsMetricCauchy,Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hv0) (ε^3) (pow_pos hε _)
  filter_upwards [he] with p hp
  have hp' : |v p.1-v p.2| < ε^3 := by
    simpa only [Real.dist_eq,sub_zero,abs_abs] using hp
  have hd : T.quotientDistance hadd hsqrt (a p.1).1 (a p.2).1 < ε :=
    (pow_lt_pow_iff_left₀ (T.quotientDistance_nonneg hadd hsqrt _ _) hε.le (by decide : 3 ≠ 0)).mp
      ((hbound p.1 p.2).trans_lt hp')
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] using hd

lemma exists_quotient_root_limit (x : Positive (T.CauchyQuotient hadd)) (hx : ‖x.1‖ ≤ 1) :
    ∃ p : T.CauchyQuotient hadd, ‖p‖ ≤ 1 ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (Positive.power (Positive.rootExponent n) x).1 p) atTop (nhds 0) :=
  T.quotient_bounded_metric_limit hadd hsqrt _ (T.quotient_roots_metricCauchy hadd hsqrt x hx) 1 zero_le_one
    (fun n => Positive.power_norm_le_one _ (Positive.rootExponent_pos n) x hx)
end CuntzPureness.PositiveQuasitrace

end

end OAI

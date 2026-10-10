import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSpectralOrder

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientSpectralCut_mul_of_le (x : selfAdjoint (T.CauchyQuotient hadd)) {s t : ℝ} (hst : s ≤ t) :
    T.quotientSpectralCut hadd hsqrt x t*T.quotientSpectralCut hadd hsqrt x s=T.quotientSpectralCut hadd hsqrt x t := by
  rcases hst.eq_or_lt with he | hlt
  · subst t; exact (T.quotientSpectralCut_spec hadd hsqrt x s).2.1
  · have hp := T.quotientSpectralCut_spec hadd hsqrt x t
    have hq := T.quotientSpectralCut_spec hadd hsqrt x s
    have hz := T.quotient_projection_separated_corners hadd hp.1 hp.2.1 hq.1 hq.2.1
      (T.quotientSpectralCuts_commute hadd hsqrt x x (Commute.refl _) t s)
      (hp.2.2.1 x.1 (Commute.refl _)) (hq.2.2.1 x.1 (Commute.refl _)) hlt hp.2.2.2.1 hq.2.2.2.2
    rw [mul_sub,mul_one] at hz
    exact (sub_eq_zero.mp hz).symm

lemma quotientSpectralCut_mul (x : selfAdjoint (T.CauchyQuotient hadd)) (s t : ℝ) :
    T.quotientSpectralCut hadd hsqrt x s*T.quotientSpectralCut hadd hsqrt x t=T.quotientSpectralCut hadd hsqrt x (max s t) := by
  rcases le_total s t with h | h
  · rw [max_eq_right h,(T.quotientSpectralCuts_commute hadd hsqrt x x (Commute.refl _) s t).eq]
    exact T.quotientSpectralCut_mul_of_le hadd hsqrt x h
  · rw [max_eq_left h]
    exact T.quotientSpectralCut_mul_of_le hadd hsqrt x h

lemma quotientSpectralCut_above_norm (x : selfAdjoint (T.CauchyQuotient hadd)) {t : ℝ} (ht : ‖x.1‖ < t) :
    T.quotientSpectralCut hadd hsqrt x t=0 := by
  have hp := T.quotientSpectralCut_spec hadd hsqrt x t
  have hx : x.1 ≤ ‖x.1‖ • (1 : T.CauchyQuotient hadd) := by
    exact x.2.le_algebraMap_norm_self.trans_eq
      (Algebra.algebraMap_eq_smul_one ‖x.1‖)
  have hz := T.quotient_projection_separated_corners hadd hp.1 hp.2.1
    (show IsSelfAdjoint (0 : T.CauchyQuotient hadd) from by simp [IsSelfAdjoint])
    (by simp : (0 : T.CauchyQuotient hadd)*0=0) (Commute.zero_right _) (hp.2.2.1 x.1 (Commute.refl _))
    (Commute.zero_left _) ht hp.2.2.2.1 (by simpa only [sub_zero,one_mul] using hx)
  simpa only [sub_zero,mul_one] using hz

lemma quotientSpectralCut_below_neg_norm (x : selfAdjoint (T.CauchyQuotient hadd)) {s : ℝ} (hs : s < -‖x.1‖) :
    T.quotientSpectralCut hadd hsqrt x s=1 := by
  have hq := T.quotientSpectralCut_spec hadd hsqrt x s
  have hx : -‖x.1‖ • (1 : T.CauchyQuotient hadd) ≤ x.1 := by
    have he : -‖x.1‖ • (1 : T.CauchyQuotient hadd) =
        -algebraMap ℝ (T.CauchyQuotient hadd) ‖x.1‖ :=
      (neg_smul ‖x.1‖ (1 : T.CauchyQuotient hadd)).trans
        (congrArg Neg.neg (Algebra.algebraMap_eq_smul_one ‖x.1‖)).symm
    exact he.le.trans x.2.neg_algebraMap_norm_le_self
  have hz := T.quotient_projection_separated_corners hadd
    (show IsSelfAdjoint (1 : T.CauchyQuotient hadd) from by simp [IsSelfAdjoint])
    (by simp : (1 : T.CauchyQuotient hadd)*1=1) hq.1 hq.2.1
    (Commute.one_left _) (Commute.one_left _) (hq.2.2.1 x.1 (Commute.refl _)) hs
    (by simpa only [one_mul] using hx) hq.2.2.2.2
  rw [one_mul] at hz
  exact (sub_eq_zero.mp hz).symm
end CuntzPureness.PositiveQuasitrace

end

end OAI

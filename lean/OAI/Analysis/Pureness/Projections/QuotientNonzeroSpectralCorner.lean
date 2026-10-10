import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSpectralProducts
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientSpectralCut_nonzero_of_lt_norm
    (a : Positive (T.CauchyQuotient hadd)) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < ‖a.1‖) :
    T.quotientSpectralCut hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ t ≠ 0 := by
  intro hz
  have h := (T.quotientSpectralCut_spec hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ t).2.2.2.2
  rw [hz, sub_zero, one_mul] at h
  have hn : ‖a.1‖ ≤ t := (CStarAlgebra.norm_le_iff_le_algebraMap a.1 ht0 a.2).mpr
    (h.trans_eq (Algebra.algebraMap_eq_smul_one t).symm)
  exact ht.not_ge hn

lemma quotientSpectralCut_le_support
    (x : selfAdjoint (T.CauchyQuotient hadd)) (q : T.CauchyQuotient hadd)
    (hq : IsStarProjection q) (hqx : q*x.1=x.1) {t : ℝ} (ht : 0 < t) :
    T.quotientSpectralCut hadd hsqrt x t ≤ q := by
  let e := T.quotientSpectralCut hadd hsqrt x t
  have he := T.quotientSpectralCut_spec hadd hsqrt x t
  have hxq : x.1*q=x.1 := by
    simpa only [star_mul, x.2.star_eq, hq.isSelfAdjoint.star_eq] using congrArg star hqx
  have hqc : Commute q x.1 := hqx.trans hxq.symm
  have heq : Commute e q := he.2.2.1 q hqc.symm
  have hz := T.quotient_projection_separated_corners hadd he.1 he.2.1
    hq.isSelfAdjoint hq.isIdempotentElem.eq heq
    (he.2.2.1 x.1 (Commute.refl _)) hqc ht he.2.2.2.1 (by
      simp only [sub_mul, one_mul, hqx, sub_self]
      exact (zero_smul ℝ (1-q)).symm.le)
  apply (IsStarProjection.le_iff_mul_eq_left ⟨he.2.1,he.1⟩ hq).mpr
  rw [mul_sub, mul_one, sub_eq_zero] at hz
  exact hz.symm

include hsqrt in

theorem exists_quotient_nonzero_spectral_corner
    (a : Positive (T.CauchyQuotient hadd)) (ha : a.1 ≠ 0)
    (q : T.CauchyQuotient hadd) (hq : IsStarProjection q) (hqa : q*a.1=a.1) :
    ∃ (t : ℝ) (e : T.CauchyQuotient hadd), 0 < t ∧ IsStarProjection e ∧ e ≠ 0 ∧
      e ≤ q ∧ Commute e a.1 ∧ t • e ≤ e*a.1 := by
  let t := ‖a.1‖/2
  have ht : 0 < t := half_pos (norm_pos_iff.mpr ha)
  have htn : t < ‖a.1‖ := half_lt_self (norm_pos_iff.mpr ha)
  let e := T.quotientSpectralCut hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ t
  have he := T.quotientSpectralCut_spec hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ t
  exact ⟨t,e,ht,⟨he.2.1,he.1⟩,T.quotientSpectralCut_nonzero_of_lt_norm hadd hsqrt a ht.le htn,
    T.quotientSpectralCut_le_support hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ q hq hqa ht,
    he.2.2.1 a.1 (Commute.refl _),he.2.2.2.1⟩
end CuntzPureness.PositiveQuasitrace

end

end OAI

import OAI.Analysis.Pureness.States.QuotientCommutingAdditivity
import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def quotientPositiveQuasitrace : CuntzPureness.PositiveQuasitrace (T.CauchyQuotient hadd) where
  toFun a := (T.quotientValue hadd hsqrt a.1).re
  nonneg a := (Complex.nonneg_iff.mp (T.quotientValue_nonneg hadd hsqrt a)).1
  map_zero := by simp only [Positive.zero,T.quotientValue_zero,Complex.zero_re]
  map_add_commute a b h := congrArg Complex.re
    (T.quotientValue_add_commute hadd hsqrt ⟨a.1,a.2.isSelfAdjoint⟩ ⟨b.1,b.2.isSelfAdjoint⟩ h)
  map_smul r a := T.quotientValue_real_smul_re hadd hsqrt r a.1
  polar x := congrArg Complex.re (T.quotientValue_polar hadd hsqrt x)
  monotone a b h := (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt h)).1

lemma quotientPositiveQuasitrace_selfAdjointValue (x : selfAdjoint (T.CauchyQuotient hadd)) :
    (T.quotientPositiveQuasitrace hadd hsqrt).selfAdjointValue x = (T.quotientValue hadd hsqrt x.1).re := by
  rw [(T.quotientPositiveQuasitrace hadd hsqrt).selfAdjointValue_shift x ‖x.1‖ (norm_nonneg _) le_rfl]
  change (T.quotientValue hadd hsqrt (x.1+‖x.1‖ • 1)).re -
    ‖x.1‖*(T.quotientValue hadd hsqrt 1).re = (T.quotientValue hadd hsqrt x.1).re
  rw [T.quotientValue_selfAdjoint_shift]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma quotientPositiveQuasitrace_complexValue (x : T.CauchyQuotient hadd) :
    (T.quotientPositiveQuasitrace hadd hsqrt).complexValue x = T.quotientValue hadd hsqrt x := by
  have he (a : selfAdjoint (T.CauchyQuotient hadd)) :
      (((T.quotientValue hadd hsqrt a.1).re : ℝ) : ℂ)=T.quotientValue hadd hsqrt a.1 := by
    apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im,T.quotientValue_selfAdjoint_im]
  have h := T.quotientValue_real_add_I hadd hsqrt (ℜ x) (ℑ x)
  rw [realPart_add_I_smul_imaginaryPart] at h
  simpa only [complexValue,T.quotientPositiveQuasitrace_selfAdjointValue,he] using h.symm

def quotientComplexQuasitrace : CuntzPureness.ComplexQuasitrace (T.CauchyQuotient hadd) :=
  (T.quotientPositiveQuasitrace hadd hsqrt).toComplex

lemma quotientComplexQuasitrace_eq (x : T.CauchyQuotient hadd) :
    T.quotientComplexQuasitrace hadd hsqrt x = T.quotientValue hadd hsqrt x :=
  T.quotientPositiveQuasitrace_complexValue hadd hsqrt x
end CuntzPureness.PositiveQuasitrace

end

end OAI

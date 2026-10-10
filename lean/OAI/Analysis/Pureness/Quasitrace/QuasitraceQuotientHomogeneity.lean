import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientOrder
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetric

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

omit [Nontrivial D] in
lemma complexValue_real_smul (r : ℝ) (x : D) :
    T.complexValue (r • x) = (r : ℂ)*T.complexValue x := by
  simp only [complexValue,_root_.map_smul,T.selfAdjointValue_smul,Complex.ofReal_mul]
  ring

lemma cauchyValue_real_smul (r : ℝ) (u : T.cauchySequenceAlgebra hadd) :
    T.cauchyValue hadd hsqrt (r • u) = (r : ℂ)*T.cauchyValue hadd hsqrt u := by
  have h1 := T.cauchyValue_tendsto hadd hsqrt (r • u)
  have h2 := (T.cauchyValue_tendsto hadd hsqrt u).const_mul (r : ℂ)
  have he (k : ℕ) : T.complexValue ((r • u).1 k) = (r : ℂ)*T.complexValue (u.1 k) :=
    T.complexValue_real_smul r (u.1 k)
  simp only [he] at h1
  exact tendsto_nhds_unique h1 h2

lemma quotientValue_real_smul (r : ℝ) (x : T.CauchyQuotient hadd) :
    T.quotientValue hadd hsqrt (r • x) = (r : ℂ)*T.quotientValue hadd hsqrt x := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  have hm : T.cauchyQuotientMap hadd (r • u) = r • T.cauchyQuotientMap hadd u :=
    _root_.map_smul ((T.cauchyQuotientMap hadd).restrictScalars ℝ) r u
  rw [← hm,T.quotientValue_map,T.quotientValue_map]
  exact T.cauchyValue_real_smul hadd hsqrt r u

lemma quotientValue_real_smul_re (r : ℝ) (x : T.CauchyQuotient hadd) :
    (T.quotientValue hadd hsqrt (r • x)).re = r*(T.quotientValue hadd hsqrt x).re := by
  rw [T.quotientValue_real_smul]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
end CuntzPureness.PositiveQuasitrace

end

end OAI

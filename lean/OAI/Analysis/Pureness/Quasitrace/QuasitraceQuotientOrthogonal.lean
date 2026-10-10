import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRootCauchy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_orthogonal_add (a b : Positive (T.CauchyQuotient hadd)) (hab : a.1*b.1=0) :
    T.quotientValue hadd hsqrt (a.1+b.1) = T.quotientValue hadd hsqrt a.1+T.quotientValue hadd hsqrt b.1 := by
  let z : selfAdjoint (T.CauchyQuotient hadd) := ⟨a.1-b.1,a.2.isSelfAdjoint.sub b.2.isSelfAdjoint⟩
  have he := CFC.posPart_negPart_unique (a := z.1) rfl hab a.2 b.2
  have hp : cfc (fun t : ℝ => t⁺) z.1=a.1 := by
    rw [← cfcₙ_eq_cfc (hf0 := by simp)]
    exact he.1
  have hn : cfc (fun t : ℝ => t⁻) z.1=b.1 := by
    rw [← cfcₙ_eq_cfc (hf0 := by simp)]
    exact he.2
  have ht := T.quotientValue_cfc_add hadd hsqrt z (fun t : ℝ => t⁺) (fun t : ℝ => t⁻)
    (by change Continuous (fun t : ℝ => max t 0); fun_prop)
    (by change Continuous (fun t : ℝ => max (-t) 0); fun_prop)
  simpa only [hp,hn] using ht

lemma quotientValue_orthogonal_sub (a b : Positive (T.CauchyQuotient hadd)) (hab : a.1*b.1=0) :
    T.quotientValue hadd hsqrt (a.1-b.1) = T.quotientValue hadd hsqrt a.1-T.quotientValue hadd hsqrt b.1 := by
  let z : selfAdjoint (T.CauchyQuotient hadd) := ⟨a.1-b.1,a.2.isSelfAdjoint.sub b.2.isSelfAdjoint⟩
  have he := CFC.posPart_negPart_unique (a := z.1) rfl hab a.2 b.2
  have hp : cfc (fun t : ℝ => t⁺) z.1=a.1 := by
    rw [← cfcₙ_eq_cfc (hf0 := by simp)]
    exact he.1
  have hn : cfc (fun t : ℝ => t⁻) z.1=b.1 := by
    rw [← cfcₙ_eq_cfc (hf0 := by simp)]
    exact he.2
  have ht := T.quotientValue_cfc_sub hadd hsqrt z (fun t : ℝ => t⁺) (fun t : ℝ => t⁻)
    (by change Continuous (fun t : ℝ => max t 0); fun_prop)
    (by change Continuous (fun t : ℝ => max (-t) 0); fun_prop)
  simpa only [hp,hn] using ht
end CuntzPureness.PositiveQuasitrace

end

end OAI

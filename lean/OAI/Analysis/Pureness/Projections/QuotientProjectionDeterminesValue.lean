import OAI.Analysis.Pureness.Projections.QuotientFiniteSpectralApproximation
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFiniteSpectrumValue
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNormContinuity
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace ComplexStarModule
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

theorem scaled_quotientValue_selfAdjoint_eq_of_projections
    (L : T.CauchyQuotient hadd →ₚ[ℂ] ℂ) (c : ℂ)
    (hproj : ∀ p : T.CauchyQuotient hadd, IsStarProjection p →
      L p = c*T.quotientValue hadd hsqrt p)
    (x : selfAdjoint (T.CauchyQuotient hadd)) : L x.1 = c*T.quotientValue hadd hsqrt x.1 := by
  have hclosed : IsClosed {z | L z = c*T.quotientValue hadd hsqrt z} :=
    isClosed_eq (map_continuous L) (continuous_const.mul (T.quotientValue_norm_continuous hadd hsqrt))
  have hx : x.1 ∈ closure {z | L z = c*T.quotientValue hadd hsqrt z} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N,e,r,hp,ho,hu,_,hn⟩ := T.exists_quotient_finite_spectral_approximation hadd hsqrt x hε
    refine ⟨∑ i ∈ Finset.range N, r i • e i, ?_, ?_⟩
    · change L (∑ i ∈ Finset.range N, r i • e i) =
        c*T.quotientValue hadd hsqrt (∑ i ∈ Finset.range N, r i • e i)
      rw [T.quotientValue_weighted_partition hadd hsqrt (Finset.range N) e
        (fun i _ => (hp i).2.2) (fun i _ j _ hij => ho i j hij) hu,
        Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [L.map_smul_of_tower, hproj (e i) ⟨(hp i).2.1, (hp i).1⟩]
      change (r i : ℂ)*(c*T.quotientValue hadd hsqrt (e i)) =
        c*((r i : ℂ)*T.quotientValue hadd hsqrt (e i))
      ring
    · simpa only [dist_eq_norm] using hn
  rwa [hclosed.closure_eq] at hx

theorem scaled_quotientValue_eq_of_projections
    (L : T.CauchyQuotient hadd →ₚ[ℂ] ℂ) (c : ℂ)
    (hproj : ∀ p : T.CauchyQuotient hadd, IsStarProjection p →
      L p = c*T.quotientValue hadd hsqrt p)
    (x : T.CauchyQuotient hadd) : L x = c*T.quotientValue hadd hsqrt x := by
  have hr := T.scaled_quotientValue_selfAdjoint_eq_of_projections hadd hsqrt L c hproj (ℜ x)
  have hi := T.scaled_quotientValue_selfAdjoint_eq_of_projections hadd hsqrt L c hproj (ℑ x)
  have hv := T.quotientValue_real_add_I hadd hsqrt (ℜ x) (ℑ x)
  rw [realPart_add_I_smul_imaginaryPart] at hv
  have hL : L x = L (ℜ x).1 + Complex.I * L (ℑ x).1 := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    rw [map_add, _root_.map_smul]
    rfl
  rw [hL, hr, hi, hv]
  ring
end CuntzPureness.PositiveQuasitrace

end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKFiniteInterpolation
import OAI.Probability.SKBarriers.Interpolation.SKSmallField
import OAI.Probability.SKBarriers.Interpolation.AdaptiveEndpointAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem exists_sk_finite_endpoint {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      (∀ j, η ≤ cumulativeGapMap k Q j) ∧
      (∀ j, Q j ≤ 1+((k+1:ℕ):ℝ)*η) ∧
      skAdaptivePressure N k β Q 1+
        (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+2*(((k+1:ℕ):ℝ)*η)) ≤
        skBlockRoot N k β (fun _ => 0)/(N:ℝ) := by
  obtain ⟨q,h0,_hD,hgap,hupper,hpath⟩ := exists_sk_finite_interpolation hN hk hβ hη hsmall
  have ha (j : Fin (k+1)) : ((j.val:ℝ)+1)*η ∈ Set.Icc 0 (((k+1:ℕ):ℝ)*η) := by
    constructor
    · positivity
    · apply mul_le_mul_of_nonneg_right _ hη.le
      exact_mod_cast j.isLt
  have hQ (j : Fin (k+1)) : q 1 j ≤ 1+((k+1:ℕ):ℝ)*η := by
    have H := hupper 1 (by norm_num) j
    linarith [(ha j).2]
  refine ⟨q 1,hgap 1 (by norm_num),hQ,?_⟩
  apply adaptive_endpoint_lower_algebra (Fin.last k) (fun _ => ((k+1:ℕ):ℝ)⁻¹)
    (q 1) (fun j => ((j.val:ℝ)+1)*η) (fun _ => by positivity) (uniformAtom_sum k)
    (by positivity) (by positivity) ha hQ
  · simpa only [h0] using hpath
  · have H := skAdaptivePressure_initial_cost (k := k) hN β hη
    convert H using 1; ring
end SK.Analytic

end
end

end

end OAI

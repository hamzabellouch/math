import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformFibers

namespace OAI

namespace Balanced.AlignedListProbability
noncomputable section
attribute [local instance] Classical.propDecidable

theorem filter_outer_ratio {Ω : Type*} (p : PMF Ω) (C E : Set Ω)
    (h : ∃ x ∈ C, x ∈ p.support) :
    (p.filter C h).toOuterMeasure E =
      p.toOuterMeasure (C ∩ E) / p.toOuterMeasure C := by
  simp only [PMF.toOuterMeasure_apply, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x
  by_cases hc : x ∈ C <;> by_cases he : x ∈ E <;>
    simp [Set.indicator, hc, he]

theorem supported_real_ne_zero {Ω : Type*} (p : PMF Ω) (C : Set Ω)
    (h : ∃ x ∈ C, x ∈ p.support) : (p.toOuterMeasure C).toReal ≠ 0 := by
  apply ENNReal.toReal_ne_zero.mpr
  constructor
  · intro hz
    have hd := (p.toOuterMeasure_apply_eq_zero_iff C).mp hz
    obtain ⟨x, hx, hs⟩ := h
    exact Set.disjoint_left.mp hd hs hx
  · rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top C

theorem marginal_conditional_ratio {Ω Y : Type*} (p : PMF Ω) (q : PMF Y)
    (C : Set Ω) (hC : ∃ x ∈ C, x ∈ p.support) (f : Ω → Y)
    (hm : (p.filter C hC).map f = q) (B E : Set Y) :
    (p.toOuterMeasure (C ∩ f ⁻¹' (B ∩ E))).toReal /
        (p.toOuterMeasure (C ∩ f ⁻¹' B)).toReal =
      (q.toOuterMeasure (B ∩ E)).toReal / (q.toOuterMeasure B).toReal := by
  have ht (K : Set Y) :
      (p.toOuterMeasure (C ∩ f ⁻¹' K)).toReal / (p.toOuterMeasure C).toReal =
        (q.toOuterMeasure K).toReal := by
    have h := congrArg (fun law => (law.toOuterMeasure K).toReal) hm
    rw [PMF.toOuterMeasure_map_apply, filter_outer_ratio, ENNReal.toReal_div] at h
    exact h
  calc
    _ = ((p.toOuterMeasure (C ∩ f ⁻¹' (B ∩ E))).toReal /
          (p.toOuterMeasure C).toReal) /
        ((p.toOuterMeasure (C ∩ f ⁻¹' B)).toReal /
          (p.toOuterMeasure C).toReal) :=
      (div_div_div_cancel_right₀ (supported_real_ne_zero p C hC) _ _).symm
    _ = _ := by rw [ht, ht]

end
end Balanced.AlignedListProbability

end OAI

import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.Modular.WeightedQuery
import OAI.Probability.CriticalPercolation.Modular.WeightedIntegralBand

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.SearchTree
variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma lintegral_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (ht : t.Valid ∅) (p : unitInterval) (B : ℝ) (hB : 0≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal (|(t.takeQuadratic a B).weightedSum a p ω|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ ENNReal.ofReal (5*B^2) := by
  have h0 (ω : Set E) : (|(t.takeQuadratic a B).weightedSum a p ω|)^4 =
      ((t.takeQuadratic a B).weightedSum a p ω)^4 := by rw [pow_abs,abs_of_nonneg (by positivity)]
  simp only [←ENNReal.ofReal_pow (abs_nonneg _),h0]
  rw [←ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall (fun _ => by positivity)),BernoulliProduct.integral_law_eq_expect]
  apply ENNReal.ofReal_le_ofReal
  exact expected_takeQuadratic_fourth a t ∅ ht p p.2 _
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ _ => ⟨by simp [BernoulliProduct.bitWeight],by simp [BernoulliProduct.bitWeight]⟩) B hB

end CriticalPercolation.SearchTree
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma lintegral_restrict (p : unitInterval) (s : Set E)
    (F : Set s → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω : Set E, F (Subtype.val ⁻¹' ω) ∂law (fun _ => p)) =
      ∫⁻ ω : Set s, F ω ∂law (fun _ => p) := by
  rw [←law_map_restrict (fun _ : E => p) s]
  exact (lintegral_map hF (Measurable.of_eval (fun edge => measurable_set_mem edge.val))).symm

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.SearchTree
variable {E R : Type*}

theorem restricted_weighted_event_fourth (s : Set E) [Fintype s] [DecidableEq s]
    (a : s → ℝ) (t : SearchTree s R) (ht : t.Valid ∅) (p : unitInterval)
    (B : ℝ) (hB : 0≤B) (h : Set E → ℝ≥0∞) (hm : Measurable h) (hh1 : ∀ ω, h ω≤1)
    (hcost : ∀ ω, h ω≠0 → t.quadraticCost a (Subtype.val ⁻¹' ω)≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω
      ∂BernoulliProduct.law (fun _ => p))^4 ≤
      ENNReal.ofReal (5*B^2)*(∫⁻ ω, h ω ∂BernoulliProduct.law (fun _ => p))^3 := by
  let f : Set E → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|
  have hf0 : Measurable (fun η : Set s =>
      ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|) := measurable_of_finite _
  have hf : Measurable f := hf0.comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))
  have heq : (fun ω : Set E => ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω) =
      fun ω => f ω*h ω := by
    funext ω
    by_cases hh : h ω=0
    · simp [hh]
    · rw [show f ω= ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| by
        dsimp only [f]
        exact congrArg (fun z : ℝ => ENNReal.ofReal |z|)
          (t.takeQuadratic_sum_eq a p B (fun e => e.val∈ω) (hcost ω hh))]
  rw [heq]
  apply (CriticalPercolation.lintegral_fractional_fourth _ f h hf.aemeasurable hm.aemeasurable hh1).trans
  apply mul_le_mul_left
  change (∫⁻ ω : Set E, (ENNReal.ofReal
    |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ _
  rw [BernoulliProduct.lintegral_restrict p s
    (fun η : Set s => (ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|)^4)
    (measurable_of_finite _)]
  exact lintegral_takeQuadratic_fourth a t ht p B hB

end CriticalPercolation.SearchTree
end
end

end OAI

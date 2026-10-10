import OAI.Analysis.LipschitzHilbert.Estimates.FiniteCarlesonEmbedding

namespace OAI

/-! The finite Carleson embedding applied to actual local product energies.
A common maximal-function majorant controls all low-frequency factors. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem carleson_product_energy (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (w : ι → X → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, w i x ∂mu else 0)≤C*mu (Q j))
    (h : ι → X → ℂ) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (G : X → ℝ) (hG : Measurable G)
    (hh : ∀ i, ∀ x∈Q i, ‖h i x‖≤v i)
    (hvG : ∀ i, ∀ x∈Q i, v i≤G x) :
    (∑ i, ∫⁻ x in Q i, w i x*ENNReal.ofReal (‖h i x‖^2) ∂mu)≤
      C*∫⁻ x, ENNReal.ofReal (G x^2) ∂mu := by
  calc
    _ ≤ ∑ i, (∫⁻ x in Q i, w i x ∂mu)*ENNReal.ofReal (v i^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hQ i)] with x hx
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (hh i x hx) 2))
    _ ≤ _ := finite_carleson_embedding Q mu hQ hlam
      (fun i => ∫⁻ x in Q i, w i x ∂mu) C hcar (fun i => v i^2)
      (fun _ => sq_nonneg _) (fun x => G x^2) (hG.pow_const 2)
      (fun _ => sq_nonneg _) (fun i x hx => pow_le_pow_left₀ (hv i) (hvG i x hx) 2)

theorem carleson_product_energy_ae (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (w : ι → X → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, w i x ∂mu else 0)≤C*mu (Q j))
    (h : ι → X → ℂ) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (G : X → ℝ) (hG : Measurable G)
    (hh : ∀ i, ∀ x∈Q i, ‖h i x‖≤v i)
    (hvG : ∀ i, ∀ᵐ x ∂mu.restrict (Q i), v i≤G x) :
    (∑ i, ∫⁻ x in Q i, w i x*ENNReal.ofReal (‖h i x‖^2) ∂mu)≤
      C*∫⁻ x, ENNReal.ofReal (G x^2) ∂mu := by
  calc
    _ ≤ ∑ i, (∫⁻ x in Q i, w i x ∂mu)*ENNReal.ofReal (v i^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hQ i)] with x hx
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (hh i x hx) 2))
    _ ≤ _ := finite_carleson_embedding_ae Q mu hQ hlam
      (fun i => ∫⁻ x in Q i, w i x ∂mu) C hcar (fun i => v i^2)
      (fun _ => sq_nonneg _) (fun x => G x^2) (hG.pow_const 2)
      (fun _ => sq_nonneg _) (fun i => (hvG i).mono (fun _ hx => pow_le_pow_left₀ (hv i) hx 2))

end LipschitzHilbert

end

end OAI

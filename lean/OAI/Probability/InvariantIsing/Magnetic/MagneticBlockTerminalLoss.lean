import OAI.Probability.InvariantIsing.Fields.FieldProductSpinAveraging
import OAI.Probability.InvariantIsing.Fields.FieldCanonicalVectorMoments

namespace OAI

/-! The actual averaged constrained terminal loss, with constants
independent of the number of Gaussian steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma magnetic_projection_distance_mean {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) :
    (∫ z, fieldProjectionDistance (spinGroupProjection group k hk) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ∑ a, Real.sqrt (spinGroupSize group a) := by
  have he := field_product_spin_average
    (fun i : Fin N => fieldCanonicalEndpointLaw h (magneticBias h (m (group i))))
    (fun σ => (hammingDist σ (spinGroupProjection group k hk σ) : ℝ))
  simp only [← fieldCanonicalSpinLaw_endpoint] at he
  exact he.trans_le (magneticCanonical_projection_distance group k hk m hm hcount h)

theorem magnetic_block_terminal_loss {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal (spinGroupSlice group k) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
          (ε⁻¹ + t) * (∑ a, Real.sqrt (spinGroupSize group a)) +
          N * Real.log (1 + Real.exp (-t)) := by
  have hl := field_projection_mean_loss (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) (spinGroupProjection group k hk)
    (spinGroupProjection_mem group k hk)
    (fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i))))
    (fieldCanonicalVectorLaw_square_integrable h (fun i => magneticBias h (m (group i)))) hε t
  have hM := fieldCanonicalVectorLaw_second_moment h
    (fun i => magneticBias h (m (group i))) hB hH
  have hD := magnetic_projection_distance_mean group k hk m hm hcount h
  exact hl.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hM hε.le)
    (mul_le_mul_of_nonneg_left hD (by positivity))) le_rfl)

lemma sum_sqrt_spinGroupSize_le {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) :
    (∑ a, Real.sqrt (spinGroupSize group a)) ≤ Fintype.card A * Real.sqrt N := by
  calc
    _ ≤ ∑ _a : A, Real.sqrt (N : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show spinGroupSize group a ≤ N from by
        simpa only [spinGroupSize, Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_le (s := (Finset.univ : Finset (Fin N))) (fun i => group i = a))
    _ = _ := by simp

theorem magnetic_block_terminal_loss_size {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal (spinGroupSlice group k) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
          (ε⁻¹ + t) * (Fintype.card A * Real.sqrt N) +
          N * Real.log (1 + Real.exp (-t)) :=
  (magnetic_block_terminal_loss group k hk m hm hcount h hB hH hε ht).trans
    (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sum_sqrt_spinGroupSize_le group) (by positivity))) le_rfl)

end InvariantIsing

end

end OAI

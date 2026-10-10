import OAI.Analysis.IrrationalRotation.Product.IndependentAngles
import OAI.Analysis.IrrationalRotation.Analysis.BlockReciprocalSum
import OAI.Analysis.IrrationalRotation.Analysis.ConsecutiveBlocks

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace InvariantProjection.IndependentAngles

theorem exists_summable_block_angles (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ i : Σ j, Fin (m j), e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val) ∧
      (∀ i, θ i ∈ Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1))) ∧
      Summable θ ∧ (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ) := by
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv m hm
  let N : ℕ → ℝ := fun i => (m (e i).1 : ℝ) * K (e i).1
  have hN : ∀ i, 0 < N i := fun i =>
    mul_pos (Nat.cast_pos.mpr (hm (e i).1)) (hK (e i).1)
  have hblock := enumerated_block_reciprocal m hm K hK hsum e
  have hNs : Summable (fun i => 1 / N i) := hblock.1
  obtain ⟨θ, hθ, hsθ, htθ, hlθ, _⟩ :=
    exists_prescribed_summable_independent_and N hN hNs
      (P := fun _ => True) (Filter.Eventually.of_forall fun _ => True.intro)
  refine ⟨e, θ, he, hθ, hsθ, ?_, hlθ⟩
  change (∑' i, θ i) ≤ 2 * (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) at htθ
  simpa only [hblock.2] using htθ

theorem exists_summable_block_angles_unitInterval
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ i : Σ j, Fin (m j), e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val) ∧
      (∀ i, θ i ∈ Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1))) ∧
      (∀ i, 0 < θ i ∧ θ i < 1) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ) := by
  obtain ⟨e, θ, he, hθ, hsθ, htθ, hlθ⟩ := exists_summable_block_angles m hm K hK hsum
  refine ⟨e, θ, he, hθ, ?_, hsθ, htθ, hlθ⟩
  intro i
  have hN : 0 < (m (e i).1 : ℝ) * K (e i).1 :=
    mul_pos (Nat.cast_pos.mpr (hm (e i).1)) (hK (e i).1)
  exact ⟨lt_of_lt_of_le (one_div_pos.mpr hN) (hθ i).1,
    lt_of_le_of_lt (hθ i).2 ((div_lt_one hN).mpr (hscale (e i).1))⟩

end InvariantProjection.IndependentAngles

end OAI

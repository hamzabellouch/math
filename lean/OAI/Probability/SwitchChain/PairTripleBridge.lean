import OAI.Probability.SwitchChain.TripleProjectionBridge
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.TripleProjectionBridge

theorem square_of_card_three_centered_row_variance
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hcard : Fintype.card ι = 3) (P : ι → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  have hv : ∀ x, ‖∑ j : Fin 3, P (e.symm j) (x - C x)‖ ^ 2 ≤
      2 * ∑ j : Fin 3, ‖P (e.symm j) (x - C x)‖ ^ 2 := by
    intro x
    rw [e.symm.sum_comp (fun i => P i (x - C x)),
      e.symm.sum_comp (fun i => ‖P i (x - C x)‖ ^ 2)]
    exact hvar x
  have h := triple_square_of_centered_row_variance
    (fun j => P (e.symm j)) C (fun j => hsymm (e.symm j))
    (fun j => hidem (e.symm j)) (fun j => hfix (e.symm j)) hv
  intro x
  simpa only [e.symm.sum_comp (fun i => x - P i x)] using h x

end Problem315.TripleProjectionBridge

namespace Problem315.PairResampling

theorem triple_fluctuation_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (a : ι → Finset (Fin n))
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ i f, expectation n d (a i) (C f) = C f)
    (hvar : ∀ f, ‖∑ i, expectation n d (a i) (f - C f)‖ ^ 2 ≤
      2 * ∑ i, ‖expectation n d (a i) (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ i, fluctuation n d (a i) f⟫ ≤
      ‖∑ i, fluctuation n d (a i) f‖ ^ 2 := by
  have h := TripleProjectionBridge.square_of_card_three_centered_row_variance
    hcard (fun i => (expectation n d (a i)).toLinearMap) C
    (fun i => expectation_isSymmetric (a i))
    (fun i => expectation_idempotent (a i)) hfix hvar
  intro f
  simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using h f

theorem vertex_triple_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n)) (hT : T.card = 3)
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ a ∈ T.powersetCard 2, ∀ f, expectation n d a (C f) = C f)
    (hvar : ∀ f, ‖∑ a ∈ T.powersetCard 2, expectation n d a (f - C f)‖ ^ 2 ≤
      2 * ∑ a ∈ T.powersetCard 2, ‖expectation n d a (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  classical
  have hc : Fintype.card (T.powersetCard 2) = 3 := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    norm_num
  have hv : ∀ f, ‖∑ a : T.powersetCard 2, expectation n d a.val (f - C f)‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2, ‖expectation n d a.val (f - C f)‖ ^ 2 := by
    intro f
    rw [Finset.sum_coe_sort (T.powersetCard 2) (fun a => expectation n d a (f - C f)),
      Finset.sum_coe_sort (T.powersetCard 2) (fun a => ‖expectation n d a (f - C f)‖ ^ 2)]
    exact hvar f
  have h := triple_fluctuation_square_of_row_variance hc
    (fun a : T.powersetCard 2 => a.val) C (fun a => hfix a.val a.property) hv
  intro f
  simpa only [Finset.sum_coe_sort (T.powersetCard 2)
    (fun a => fluctuation n d a f)] using h f

end Problem315.PairResampling

end

end OAI

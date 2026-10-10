import OAI.Probability.SignedSweeps.BlockTraceBudget

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma occupied_block_type_angle_exp {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i))
    (hH : ∀ j, (H j).height ≤ q) (hK : ∀ i, (K i).height ≤ q)
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (hR : max s m+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
      pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 (Real.exp (blockEntropy H+blockEntropy K-signedEntropy a b+l+
        ((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R))) := by
  have ht := signed_word_type_angle_numbered hq
    (occupiedBoard e (markedInjection hn z)) (occupiedBoardEquiv e (markedInjection hn z))
    eH hHroute eK hKroute (fun j => (H j).size_eq)
    (fun j => (H j).2.1) (fun j => (H j).2.2)
    (fun j => (le_max_left _ _).trans (hH j))
    (fun j => (le_max_right _ _).trans (hH j))
    (fun i => (K i).size_eq) (fun i => (K i).2.1) (fun i => (K i).2.2)
    (fun i => (le_max_left _ _).trans (hK i))
    (fun i => (le_max_right _ _).trans (hK i)) h a b ha hb
  apply ht.trans
  apply min_le_min_left 1
  have hCH := blockCarrierCost_le_exp (q:=q) H hkH (by omega : s+1 ≤ R)
  have hCK := blockCarrierCost_le_exp (q:=q) K hkK (by omega : m+1 ≤ R)
  have hmissing := occupiedBoard_missing_bound hn e z
  calc
    _ ≤ (Real.exp (blockEntropy H+(Fintype.card B:ℝ)*(2*(q:ℝ)^2*Real.log R)) *
          Real.exp (blockEntropy K+(Fintype.card A:ℝ)*(2*(q:ℝ)^2*Real.log R)) *
          Real.exp (-signedEntropy a b)) * Real.exp (l:ℝ) := by
      apply mul_le_mul _ hmissing (missingCellFactor_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul hCH hCK (Finset.prod_nonneg (fun i _ => (pairCarrierCost_pos _ _ _).le))
        (Real.exp_nonneg _)
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

lemma occupied_block_type_angle_exp_all {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i))
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (hR : max s m+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
      pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 (Real.exp (blockEntropy H+blockEntropy K-signedEntropy a b+l+
        ((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R))) := by
  by_cases hH : ∀ j, (H j).height ≤ q
  · by_cases hK : ∀ i, (K i).height ≤ q
    · exact occupied_block_type_angle_exp hq hn e z eH hHroute eK hKroute H K
        hH hK hkH hkK hR h a b ha hb
    · push Not at hK
      obtain ⟨i,hi⟩ := hK
      rw [blockTypeProjection_zero_of_height eK K i (by simpa using hi)]
      simp only [mul_zero, zero_mul, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact le_min zero_le_one (Real.exp_nonneg _)
  · push Not at hH
    obtain ⟨j,hj⟩ := hH
    rw [blockTypeProjection_zero_of_height eH H j (by simpa using hj)]
    simp only [zero_mul, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact le_min zero_le_one (Real.exp_nonneg _)

end SignedSweeps
end

end OAI

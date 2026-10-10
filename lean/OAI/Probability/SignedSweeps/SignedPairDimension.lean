import OAI.Probability.SignedSweeps.HookCarrierDimension
import OAI.Probability.SignedSweeps.SignedArmDominance

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma signed_hook_prefix_dimension_lower {n Q : ℕ} (lam : Partition n)
    (hh : IsSignedHook Q lam.1) (a b : ℕ → ℕ)
    (ha : ∀ k ≤ Q, ∑ i ∈ Finset.range k, (lam.1.rowLen i - Q) ≤ ∑ i ∈ Finset.range k, a i)
    (hb : ∀ k ≤ Q, ∑ i ∈ Finset.range k, (lam.1.colLen i - Q) ≤ ∑ i ∈ Finset.range k, b i)
    (B : ℕ) (hB : 2*n+Q+1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i ∈ Finset.range Q, ((a i).factorial : ℝ)) *
      (∏ j ∈ Finset.range Q, ((b j).factorial : ℝ)) * (B : ℝ) ^ (3*(Q*Q)) := by
  have hr := factorial_product_le_of_prefix_dominance (fun i => lam.1.rowLen i-Q) a Q
    (fun i j h => Nat.sub_le_sub_right (lam.1.rowLen_anti i j h) Q) ha
  have hc := factorial_product_le_of_prefix_dominance (fun i => lam.1.colLen i-Q) b Q
    (fun i j h => Nat.sub_le_sub_right (lam.1.colLen_anti i j h) Q) hb
  have hr' : (∏ i : Fin Q, ((lam.1.rowLen i-Q).factorial : ℝ)) ≤
      ∏ i ∈ Finset.range Q, ((a i).factorial : ℝ) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((lam.1.rowLen i-Q).factorial : ℝ))]
    exact_mod_cast hr
  have hc' : (∏ i : Fin Q, ((lam.1.colLen i-Q).factorial : ℝ)) ≤
      ∏ i ∈ Finset.range Q, ((b i).factorial : ℝ) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((lam.1.colLen i-Q).factorial : ℝ))]
    exact_mod_cast hc
  apply (hook_capacity_dimension_lower lam hh _ _ (fun _ => le_rfl) (fun _ => le_rfl) B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg _)) hc'
      (Finset.prod_nonneg (by intros; positivity)) (by positivity)) (by positivity)

theorem signed_pair_dimension_factorial_lower {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x))
    (B : ℕ) (hB : 2*n+2*q+1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i ∈ Finset.range (2*q), ((a.1.rowLen i).factorial : ℝ)) *
      (∏ j ∈ Finset.range (2*q), ((b.1.rowLen j).factorial : ℝ)) * (B : ℝ) ^ (12*(q*q)) := by
  have hh := pair_signed_hook hn a b lam ha hb e f hf hint
  have hrow (k : ℕ) : ∑ i ∈ Finset.range k, (lam.1.rowLen i-2*q) ≤
      ∑ i ∈ Finset.range k, a.1.rowLen i := by
    exact (Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_left (by omega : q ≤ 2*q) _)).trans
      (pair_signed_row_prefix a b lam hb e f hf hint k)
  have hcol (k : ℕ) : ∑ i ∈ Finset.range k, (lam.1.colLen i-2*q) ≤
      ∑ i ∈ Finset.range k, b.1.rowLen i := by
    exact (Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_left (by omega : q ≤ 2*q) _)).trans
      (pair_signed_col_prefix a b lam ha e f hf hint k)
  simpa only [show 3*(2*q*(2*q)) = 12*(q*q) by ring] using
    signed_hook_prefix_dimension_lower lam hh a.1.rowLen b.1.rowLen
      (fun k _ => hrow k) (fun k _ => hcol k) B hB

lemma rowLen_zero_of_height_le (lam : YoungDiagram) {i : ℕ} (hi : lam.colLen 0 ≤ i) :
    lam.rowLen i = 0 := by
  by_contra hn
  have hm : (i,0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hn)
  have ht := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowLen_sum_range {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q) :
    ∑ i ∈ Finset.range Q, lam.1.rowLen i = n := by
  have hs : ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i = n := by
    simpa only [Fin.sum_univ_eq_sum_range (fun i => lam.1.rowLen i)] using lam.sum_rowLen
  calc
    ∑ i ∈ Finset.range Q, lam.1.rowLen i = ∑ i ∈ Finset.range (lam.1.colLen 0), lam.1.rowLen i := ?_
    _ = n := hs
  symm
  apply Finset.sum_subset (Finset.range_mono hQ)
  intro i hi hn
  exact rowLen_zero_of_height_le lam.1 (by simpa only [Finset.mem_range, not_lt] using hn)

lemma partsEntropy_rowLen_range {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q) (N : ℝ) :
    partsEntropy N lam.1.rowLens =
      ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) := by
  rw [partsEntropy_rowLen,
    Fin.sum_univ_eq_sum_range (fun i => (lam.1.rowLen i : ℝ) * Real.log (N/lam.1.rowLen i))]
  apply Finset.sum_subset (Finset.range_mono hQ)
  intro i hi hn
  rw [rowLen_zero_of_height_le lam.1 (by simpa only [Finset.mem_range, not_lt] using hn)]
  simp

lemma partsEntropy_rowLen_log {n Q : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q)
    (N : ℝ) (hN : n ≠ 0 → N ≠ 0) :
    partsEntropy N lam.1.rowLens = (n : ℝ) * Real.log N -
      ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i) := by
  rw [partsEntropy_rowLen_range lam hQ]
  have he (i : ℕ) : (lam.1.rowLen i : ℝ) * Real.log (N / lam.1.rowLen i) =
      (lam.1.rowLen i : ℝ) * Real.log N - (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i) := by
    by_cases hi : lam.1.rowLen i = 0
    · simp [hi]
    have hn : n ≠ 0 := by
      have h := rowLen_le_card lam.1 i
      rw [lam.2] at h
      omega
    rw [Real.log_div (hN hn) (Nat.cast_ne_zero.mpr hi)]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) = n := by exact_mod_cast rowLen_sum_range lam hQ
  rw [hs]

lemma log_factorial_upper_uniform (k n : ℕ) (hkn : k ≤ n) :
    Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log k - k + Real.log (n+1 : ℕ) + 1 := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul, sub_self, zero_add]
    positivity
  have ht := log_factorial_upper (Nat.pos_of_ne_zero hk)
  have hl : Real.log (k : ℝ) ≤ Real.log (n+1 : ℕ) := Real.log_le_log
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) (by exact_mod_cast hkn.trans (Nat.le_succ _))
  linarith

lemma row_log_factorials_le {n Q M : ℕ} (lam : Partition n) (hQ : lam.1.colLen 0 ≤ Q)
    (hM : n ≤ M) :
    (∑ i ∈ Finset.range Q, Real.log ((lam.1.rowLen i).factorial : ℝ)) ≤
      (∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i)) - n +
        (Q : ℝ) * (Real.log (M+1 : ℕ) + 1) := by
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range Q) =>
    log_factorial_upper_uniform (lam.1.rowLen i) M ((rowLen_le_card lam.1 i).trans (by simpa only [lam.2] using hM)))
  have hs : ∑ i ∈ Finset.range Q, (lam.1.rowLen i : ℝ) = n := by exact_mod_cast rowLen_sum_range lam hQ
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hs, mul_add, mul_one, add_assoc] using ht

theorem signed_pair_log_dimension_lower {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x))
    (B : ℕ) (hB : 2*n+2*q+1 ≤ B) :
    signedEntropy a b - 4*(q : ℝ)*(Real.log (n+1 : ℕ)+1) -
      12*(q : ℝ)^2*Real.log B ≤ Real.log (spechtDimension lam : ℝ) := by
  have hd := signed_pair_dimension_factorial_lower hn a b lam ha hb e f hf hint B hB
  have hl := Real.log_le_log (by positivity : (0:ℝ) < n.factorial) hd
  have hdim : (0:ℝ) < spechtDimension lam := by exact_mod_cast spechtDimension_pos lam
  have hbase : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_prod (fun _ _ => by positivity), Real.log_prod (fun _ _ => by positivity), Real.log_pow] at hl
  have haur := row_log_factorials_le a (ha.trans (by omega : q ≤ 2*q)) (show u ≤ n by omega)
  have hbur := row_log_factorials_le b (hb.trans (by omega : q ≤ 2*q)) (show v ≤ n by omega)
  have he : signedEntropy a b = (n : ℝ) * Real.log n -
      (∑ i ∈ Finset.range (2*q), (a.1.rowLen i : ℝ) * Real.log (a.1.rowLen i)) -
      (∑ i ∈ Finset.range (2*q), (b.1.rowLen i : ℝ) * Real.log (b.1.rowLen i)) := by
    have hh : signedEntropy a b = partsEntropy (u+v) a.1.rowLens + partsEntropy (u+v) b.1.rowLens := by
      simp only [signedEntropy, partsEntropy, List.map_append, List.sum_append]
    have hn' : (u : ℝ)+v = n := by exact_mod_cast hn
    rw [hh, hn', partsEntropy_rowLen_log (Q:=2*q) a (by omega) _ (by intro hu; exact Nat.cast_ne_zero.mpr (by omega)),
      partsEntropy_rowLen_log (Q:=2*q) b (by omega) _ (by intro hv; exact Nat.cast_ne_zero.mpr (by omega))]
    rw [← hn']
    ring
  have hn' : (u : ℝ)+v = n := by exact_mod_cast hn
  have hlow := log_factorial_lower n
  push_cast at hl haur hbur ⊢
  rw [he]
  nlinarith

end SignedSweeps
end

end OAI

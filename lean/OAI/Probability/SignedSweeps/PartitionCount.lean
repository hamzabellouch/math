import OAI.Probability.SignedSweeps.HookArms
import OAI.Probability.SignedSweeps.PairDecomposition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma diagram_rectangle_card (lam : YoungDiagram) {i j : ℕ} (h : (i,j) ∈ lam) :
    (i+1)*(j+1) ≤ lam.card := by
  have hs : Finset.range (i+1) ×ˢ Finset.range (j+1) ⊆ lam.cells := by
    intro c hc
    rcases Finset.mem_product.mp hc with ⟨hi,hj⟩
    exact lam.up_left_mem (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) h
  have ht := Finset.card_le_card hs
  simpa only [Finset.card_product, Finset.card_range, YoungDiagram.card] using ht

lemma diagram_signedHook_of_card_lt {q : ℕ} (lam : YoungDiagram)
    (h : lam.card < (q+1)^2) : IsSignedHook q lam := by
  by_contra hn
  have hm : (q,q) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hn)
  have he := diagram_rectangle_card lam hm
  rw [pow_two] at h
  omega

lemma partition_signedHook_sqrt {k n : ℕ} (lam : Partition k) (hkn : k ≤ n) :
    IsSignedHook (Nat.sqrt n) lam.1 := by
  apply diagram_signedHook_of_card_lt
  rw [lam.2]
  exact lt_of_le_of_lt hkn (Nat.lt_succ_sqrt' n)

lemma signedHook_ext {q : ℕ} {a b : YoungDiagram}
    (ha : IsSignedHook q a) (hb : IsSignedHook q b)
    (hr : ∀ i < q, a.rowLen i = b.rowLen i)
    (hc : ∀ j < q, a.colLen j = b.colLen j) : a = b := by
  apply SetLike.ext
  intro ⟨i,j⟩
  constructor
  · intro hx
    rcases signedHook_no_southeast ha hx with hi | hj
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [← hr i hi]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hx
    · apply YoungDiagram.mem_iff_lt_colLen.mpr
      rw [← hc j hj]
      exact YoungDiagram.mem_iff_lt_colLen.mp hx
  · intro hx
    rcases signedHook_no_southeast hb hx with hi | hj
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [hr i hi]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hx
    · apply YoungDiagram.mem_iff_lt_colLen.mpr
      rw [hc j hj]
      exact YoungDiagram.mem_iff_lt_colLen.mp hx

theorem partitionCount_le_uniform {k n : ℕ} (hkn : k ≤ n) :
    Fintype.card (Partition k) ≤ (n+1)^(2*Nat.sqrt n) := by
  let encode : Partition k → (Fin (Nat.sqrt n) → Fin (n+1)) × (Fin (Nat.sqrt n) → Fin (n+1)) := fun lam =>
    (fun i => ⟨lam.1.rowLen i, Nat.lt_succ_of_le ((rowLen_le_card lam.1 i).trans (by simpa only [lam.2] using hkn))⟩,
     fun i => ⟨lam.1.colLen i, Nat.lt_succ_of_le ((colLen_le_card lam.1 i).trans (by simpa only [lam.2] using hkn))⟩)
  have hi : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply signedHook_ext (partition_signedHook_sqrt a hkn) (partition_signedHook_sqrt b hkn)
    · intro i hi
      exact congrArg (fun e => (e.1 ⟨i,hi⟩).val) hab
    · intro j hj
      exact congrArg (fun e => (e.2 ⟨j,hj⟩).val) hab
  have hc := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add] using hc

lemma partitionCount_le (n : ℕ) :
    Fintype.card (Partition n) ≤ (n+1)^(2*Nat.sqrt n) := partitionCount_le_uniform le_rfl

lemma pairTypeCount_le (p : ℕ) :
    Fintype.card (PairType p) ≤ (p+1)^(4*Nat.sqrt p+1) := by
  change Fintype.card (Σ u : Fin (p+1), Partition u.1 × Partition (p-u.1)) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _u : Fin (p+1), (p+1)^(4*Nat.sqrt p) := by
      apply Finset.sum_le_sum
      intro u _
      rw [Fintype.card_prod, show 4*Nat.sqrt p = 2*Nat.sqrt p+2*Nat.sqrt p by omega, pow_add]
      exact Nat.mul_le_mul (partitionCount_le_uniform (Nat.le_of_lt_succ u.2))
        (partitionCount_le_uniform (Nat.sub_le p u.1))
    _ = _ := by simp [pow_succ, mul_comm]

lemma log_partitionCount_le (n : ℕ) :
    Real.log (Fintype.card (Partition n) : ℝ) ≤
      (2*Nat.sqrt n : ℕ)*Real.log (n+1 : ℕ) := by
  by_cases hn : Fintype.card (Partition n) = 0
  · simp only [hn, Nat.cast_zero, Real.log_zero]
    positivity
  have hp : (0:ℝ) < Fintype.card (Partition n) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have ht := Real.log_le_log hp (show (Fintype.card (Partition n) : ℝ) ≤ (n+1 : ℕ)^(2*Nat.sqrt n) by
    exact_mod_cast partitionCount_le n)
  simpa only [Real.log_pow] using ht

lemma log_pairTypeCount_le (p : ℕ) :
    Real.log (Fintype.card (PairType p) : ℝ) ≤
      (4*Nat.sqrt p+1 : ℕ)*Real.log (p+1 : ℕ) := by
  by_cases hn : Fintype.card (PairType p) = 0
  · simp only [hn, Nat.cast_zero, Real.log_zero]
    positivity
  have hp : (0:ℝ) < Fintype.card (PairType p) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have ht := Real.log_le_log hp (show (Fintype.card (PairType p) : ℝ) ≤ (p+1 : ℕ)^(4*Nat.sqrt p+1) by
    exact_mod_cast pairTypeCount_le p)
  simpa only [Real.log_pow] using ht

end SignedSweeps
end

end OAI

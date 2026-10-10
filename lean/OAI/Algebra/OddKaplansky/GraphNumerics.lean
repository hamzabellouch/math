import OAI.Algebra.OddKaplansky.BooleanPolynomial

namespace OAI

universe portUniverse1

section
noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.GraphNumerics

def binomDefinition (k : ℕ) : ℕ := Nat.choose 1200 k
opaque binomWrapped : Subtype (Eq binomDefinition) := ⟨_, rfl⟩

def binom : (k : ℕ) → ℕ := binomWrapped.1
theorem binom_def (k : ℕ) : binom k = Nat.choose 1200 k := by
  delta binom
  rw [show binomWrapped = ⟨binomDefinition, rfl⟩ from Subtype.ext binomWrapped.2.symm]
  rfl
attribute [irreducible] binom binomDefinition
attribute [eqns binom_def] binom

lemma choose_mono_small {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 600) :
    binom a ≤ binom b := by
  induction hab with
  | refl => exact le_rfl
  | @step b hab ih =>
    apply (ih (by omega)).trans
    rw [binom_def, binom_def]
    apply Nat.choose_le_succ_of_lt_half_left
    omega

lemma choose_step (k : ℕ) (hk : k ≤ 499) :
    7 * binom k ≤ 5 * binom (k+1) := by
  have he := Nat.choose_succ_right_eq 1200 k
  rw [← binom_def (k+1), ← binom_def k] at he
  have hc : 7 * (k+1) ≤ 5 * (1200-k) := by omega
  have hh := Nat.mul_le_mul_left (binom k) hc
  apply Nat.le_of_mul_le_mul_right (c := k+1)
  · nlinarith only [he, hh]
  · omega

lemma choose_growth (n : ℕ) (hn : n ≤ 100) :
    7^n * binom 400 ≤ 5^n * binom (400+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (by omega)
    have hs := choose_step (400+n) (by omega)
    calc
      _ = 7 * (7^n * binom 400) := by ring
      _ ≤ 7 * (5^n * binom (400+n)) := Nat.mul_le_mul_left _ hi
      _ = 5^n * (7 * binom (400+n)) := by ring
      _ ≤ 5^n * (5 * binom (400+n+1)) := Nat.mul_le_mul_left _ hs
      _ = _ := by simp only [pow_succ, Nat.add_assoc]; ring

lemma sum_small_bound : (∑ j ∈ Finset.range 401, binom j) ≤ 401 * binom 400 := by
  calc
    _ ≤ ∑ _j ∈ Finset.range 401, binom 400 :=
      Finset.sum_le_sum (fun j hj => choose_mono_small (by have := Finset.mem_range.mp hj; omega) (by omega))
    _ = _ := by simp

lemma ratio_bound : 100 * (∑ j ∈ Finset.range 401, binom j) < binom 600 := by
  have hg := choose_growth 100 (by omega)
  have hm := choose_mono_small (a := 500) (b := 600) (by omega) (by omega)
  have hp : 0 < binom 400 := by rw [binom_def]; exact Nat.choose_pos (by omega)
  have hc : 40100 * 5^100 < 7^100 := by norm_num
  have hsmall := sum_small_bound
  have ht := Nat.mul_le_mul_left (5^100) (Nat.mul_le_mul_left 100 hsmall)
  have hstrict := Nat.mul_lt_mul_of_pos_right hc hp
  have hlast := Nat.mul_le_mul_left (5^100) hm
  apply Nat.lt_of_mul_lt_mul_left (a := 5^100)
  nlinarith only [ht,hstrict,hg,hlast]

lemma source_ratio_bound :
    100 * (∑ j ∈ Finset.range 401, Nat.choose 1200 j) < Nat.choose 1200 600 := by
  simpa only [binom_def] using ratio_bound

variable (E : Type portUniverse1) [Fintype E]
def smallSetEquiv (n : ℕ) :
    {T : Finset E // T.card ≤ n} ≃ (Σ k : Fin (n+1), {T : Finset E // T.card = k.val}) where
  toFun T := ⟨⟨T.val.card, by omega⟩, ⟨T.val,rfl⟩⟩
  invFun v := ⟨v.2.val, by have := v.1.isLt; rw [v.2.property]; omega⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨⟨k,hk⟩,⟨T,hT⟩⟩
    change T.card = k at hT
    dsimp
    subst k
    rfl

lemma card_small_sets (n : ℕ) :
    Fintype.card {T : Finset E // T.card ≤ n} = ∑ j ∈ Finset.range (n+1), Nat.choose (Fintype.card E) j := by
  rw [Fintype.card_congr (smallSetEquiv E n), Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end OddKaplansky.GraphNumerics

end
end

end OAI

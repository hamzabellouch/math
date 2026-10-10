import Mathlib

namespace OAI

noncomputable section
open scoped Pointwise
namespace Ostmann.Characters
section Group
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem square_eq_univ_of_small_doubling (A : Finset G) (h1 : 1∈A)
    (hgen : Subgroup.closure (A : Set G) = ⊤)
    (hgrow : ((A*A).card : ℚ) < (3/2:ℚ)*A.card) : A*A = Finset.univ := by
  let H := Finset.invMulSubgroup A hgrow
  have hHcoe : (H : Set G) = (A⁻¹*A : Finset G) := by
    change (Finset.invMulSubgroup A hgrow : Set G) = _
    rw [Finset.invMulSubgroup_eq_inv_mul, Finset.coe_mul, Finset.coe_inv]
  have hle : Subgroup.closure (A : Set G) ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro x hx
    rw [hHcoe]
    exact Finset.mem_mul.mpr ⟨1, by simpa using h1, x, hx, one_mul x⟩
  have htop : H = ⊤ := top_unique (hgen ▸ hle)
  have hA : A⁻¹*A = Finset.univ := by
    ext x
    change x∈((A⁻¹*A : Finset G) : Set G) ↔ x∈Finset.univ
    rw [← hHcoe, htop]
    simp
  apply Finset.eq_univ_of_card
  rw [← Finset.card_inv_mul_of_doubling_lt_three_halves hgrow, hA, Finset.card_univ]

omit [Fintype G] in
section

def doubled (A : Finset G) : ℕ → Finset G
  | 0 => A
  | n+1 => doubled A n * doubled A n

theorem one_mem_doubled (A : Finset G) (h1 : 1∈A) (n : ℕ) : 1∈doubled A n := by
  induction n with
  | zero => exact h1
  | succ n hn => simpa only [doubled, mul_one] using Finset.mul_mem_mul hn hn

theorem subset_doubled (A : Finset G) (h1 : 1∈A) (n : ℕ) : A⊆doubled A n := by
  induction n with
  | zero => exact Set.Subset.refl _
  | succ n hn =>
    intro x hx
    simpa only [doubled, mul_one] using
      Finset.mul_mem_mul (hn hx) (one_mem_doubled A h1 n)

theorem closure_doubled (A : Finset G) (h1 : 1∈A)
    (hgen : Subgroup.closure (A : Set G) = ⊤) (n : ℕ) :
    Subgroup.closure (doubled A n : Set G) = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Subgroup.closure_mono (subset_doubled A h1 n)

theorem doubled_eq_pow (A : Finset G) (n : ℕ) : doubled A n = A^(2^n) := by
  induction n with
  | zero => simp [doubled]
  | succ n hn => rw [doubled, hn, ← pow_add, pow_succ]; congr 1; omega

end

theorem exists_doubled_eq_univ (A : Finset G) (h1 : 1∈A)
    (hgen : Subgroup.closure (A : Set G) = ⊤) (N : ℕ)
    (hN : (Fintype.card G : ℚ) < (3/2:ℚ)^N*A.card) :
    ∃ n≤N, doubled A n = Finset.univ := by
  by_contra! hn
  have hgrowth : ∀ n≤N, (3/2:ℚ)^n*A.card ≤ (doubled A n).card := by
    intro n hle
    induction n with
    | zero => simp [doubled]
    | succ n ih =>
      have hi := ih (by omega)
      have hs : (3/2:ℚ)*(doubled A n).card ≤ (doubled A (n+1)).card := by
        by_contra! hs
        exact hn (n+1) hle (square_eq_univ_of_small_doubling (doubled A n)
          (one_mem_doubled A h1 n) (closure_doubled A h1 hgen n) hs)
      rw [pow_succ]
      nlinarith
  have hb : ((doubled A N).card : ℚ) ≤ Fintype.card G := by
    exact_mod_cast Finset.card_le_univ (doubled A N)
  linarith [hgrowth N le_rfl]
end Group
end Ostmann.Characters

end

end OAI

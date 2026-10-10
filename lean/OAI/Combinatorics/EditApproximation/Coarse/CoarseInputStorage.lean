import OAI.Combinatorics.EditApproximation.Coarse.CoarseInputGuard
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRetainedValues
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem storedNaturalBits_le (values : List ℕ) (A : ℕ)
    (h : ∀ a ∈ values, Nat.size a ≤ A) :
    storedNaturalBits values ≤ 1 + values.length * (A + 1) := by
  have hs : (values.map fun a => Nat.size a + 1).sum ≤ values.length * (A + 1) := by
    induction values with
    | nil => simp
    | cons a values ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left hs 1



theorem coarsePreparedInputStorage_le (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi A : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ A) :
    coarsePreparedInputStorage source target sourceLo sourceHi targetLo targetHi ≤
      3 + (source.length + target.length) * (A + 1) := by
  have hs : storedNaturalBits (substring source sourceLo sourceHi) ≤ 1 + source.length * (A + 1) := by
    apply (storedNaturalBits_le _ A (by
      intro a ha
      exact hsymbol a (List.mem_append_left _ (List.mem_of_mem_take (List.mem_of_mem_drop ha))))).trans
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  have ht : storedNaturalBits (substring target targetLo targetHi) ≤ 1 + target.length * (A + 1) := by
    apply (storedNaturalBits_le _ A (by
      intro a ha
      exact hsymbol a (List.mem_append_right _ (List.mem_of_mem_take (List.mem_of_mem_drop ha))))).trans
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  unfold coarsePreparedInputStorage
  rw [coarsePreparedSlicesWithWork_value source target sourceLo sourceHi targetLo targetHi hslo hshi htlo hthi]
  split_ifs
  · simp only; omega
  · simp only
    nlinarith only [hs, ht]

theorem coarsePreparedInputStorage_polynomial (source target : List ℕ)
    (N sourceLo sourceHi targetLo targetHi : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) :
    coarsePreparedInputStorage source target sourceLo sourceHi targetLo targetHi ≤ (N + 2) ^ 16 := by
  have h := coarsePreparedInputStorage_le source target sourceLo sourceHi targetLo targetHi
    (inputHeight N ^ 3) hslo hshi htlo hthi hsymbol
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hH := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hH
  change inputHeight N ^ 3 ≤ X ^ 12 at hH
  have h1 : 1 ≤ X ^ 12 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul (show source.length + target.length ≤ X by dsimp only [X]; omega)
    (show inputHeight N ^ 3 + 1 ≤ 2 * X ^ 12 by omega)
  have hp : 1 ≤ X ^ 13 := one_le_pow₀ (by omega)
  have hc : 5 ≤ X ^ 3 := (by decide : 5 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hX 3)
  calc
    _ ≤ 5 * X ^ 13 := by nlinarith only [h, hm, hp]
    _ ≤ X ^ 3 * X ^ 13 := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI

import Mathlib

namespace OAI

noncomputable section
open Equiv

namespace Problem315.PermutationFactors

variable {α : Type*} [DecidableEq α]

theorem swapFactorsAux_length_le (l : List α) (σ : Perm α)
    (h : ∀ {x}, σ x ≠ x → x ∈ l) :
    (Perm.swapFactorsAux l σ h).val.length ≤ l.length := by
  induction l generalizing σ with
  | nil => simp [Perm.swapFactorsAux]
  | cons x l ih =>
    rw [Perm.swapFactorsAux]
    dsimp only
    split_ifs with hfix
    · have htail : ∀ {y}, σ y ≠ y → y ∈ l := by
        intro y hy
        exact List.mem_of_ne_of_mem (fun hyx => by simp [hyx, hfix.symm] at hy) (h hy)
      exact (ih σ htail).trans (Nat.le_succ _)
    · have htail : ∀ {y}, (swap x (σ x) * σ) y ≠ y → y ∈ l := by
        intro y hy
        have hh := Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hh.2 (h hh.1)
      simpa only [List.length_cons] using
        Nat.succ_le_succ (ih (swap x (σ x) * σ) htail)

theorem exists_swap_factors_length_le [Fintype α] (σ : Perm α) :
    ∃ l : List (Perm α), l.prod = σ ∧
      (∀ τ ∈ l, Perm.IsSwap τ) ∧ l.length ≤ Fintype.card α := by
  classical
  let support : List α := Finset.univ.toList
  have hsupport : ∀ {x}, σ x ≠ x → x ∈ support := by
    intro x _
    simp [support]
  let factors := Perm.swapFactorsAux support σ hsupport
  refine ⟨factors.val, factors.property.1, factors.property.2, ?_⟩
  have h := swapFactorsAux_length_le support σ hsupport
  simpa only [factors, support, Finset.length_toList, Finset.card_univ] using h

theorem exists_swap_pairs_of_isSwap_list (l : List (Perm α))
    (hl : ∀ τ ∈ l, Perm.IsSwap τ) :
    ∃ v : List (α × α), v.map (fun ab => swap ab.1 ab.2) = l ∧
      v.length = l.length ∧ ∀ ab ∈ v, ab.1 ≠ ab.2 := by
  induction l with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons τ l ih =>
    obtain ⟨a, b, hab, hτ⟩ := hl τ (by simp)
    obtain ⟨v, hv, hlen, hdistinct⟩ := ih (fun υ hυ => hl υ (List.mem_cons_of_mem τ hυ))
    refine ⟨(a, b) :: v, ?_, by simp [hlen], ?_⟩
    · simp [hv, hτ]
    · intro ab habv
      rcases List.mem_cons.mp habv with h | h
      · simpa [h] using hab
      · exact hdistinct ab h

theorem exists_swap_pair_factors_length_le [Fintype α] (σ : Perm α) :
    ∃ l : List (α × α), (l.map (fun ab => swap ab.1 ab.2)).prod = σ ∧
      l.length ≤ Fintype.card α ∧ ∀ ab ∈ l, ab.1 ≠ ab.2 := by
  obtain ⟨factors, hprod, hswap, hlen⟩ := exists_swap_factors_length_le σ
  obtain ⟨l, hl, hlen', hdistinct⟩ := exists_swap_pairs_of_isSwap_list factors hswap
  exact ⟨l, by rw [hl, hprod], hlen' ▸ hlen, hdistinct⟩

end Problem315.PermutationFactors

end

end OAI

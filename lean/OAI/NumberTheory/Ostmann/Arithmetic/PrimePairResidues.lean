import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals

namespace OAI

/-! # The original two giant sums as a finite residue-pair sum -/

namespace Ostmann
open scoped BigOperators Classical

theorem finite_pair_comparison {A B : Type*} (S : Finset A) (T : Finset B)
    (F G : A → B → ℂ) (δ : ℝ) (h : ∀ a ∈ S, ∀ b ∈ T, ‖F a b - G a b‖ ≤ δ) :
    ‖(∑ a ∈ S, ∑ b ∈ T, F a b) - (∑ a ∈ S, ∑ b ∈ T, G a b)‖ ≤
      (S.card : ℝ) * T.card * δ := by
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ S, ‖∑ b ∈ T, (F a b - G a b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, ∑ b ∈ T, δ := by
      apply Finset.sum_le_sum
      intro a ha
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => h a ha b hb)
    _ = _ := by simp; ring

theorem prime_pair_residue_factorization (q : ℕ) (hq : 0 < q) (u v r s : ℝ)
    (hu : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, p.Prime → q < p)
    (hr : ∀ p ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, p.Prime → q < p)
    (F : ℕ → ℕ → ℂ) (c : ℕ → ℕ → ℂ) (H : ℝ → ℝ → ℂ)
    (hfactor : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, p.Prime →
      ∀ t ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, t.Prime →
      ∀ a ∈ reducedResidues q, ∀ b ∈ reducedResidues q,
      Nat.ModEq q p a → Nat.ModEq q t b →
      F p t = c a b * H (Real.log p) (Real.log t)) :
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
        complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v
          (fun x => c a b * H x y)) := by
  rw [complexPrimeInterval_residues q hq r s hr]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← complexPrimeInterval_finset_sum]
  apply complexPrimeInterval_congr
  intro t ht hprime htb
  have ht0 : (0 : ℝ) < t := by exact_mod_cast hprime.pos
  rw [Real.exp_log ht0, Nat.floor_natCast, complexPrimeInterval_residues q hq u v hu]
  apply Finset.sum_congr rfl
  intro a ha
  apply complexPrimeInterval_congr
  intro p hp hpp hpa
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [Real.exp_log hp0, Nat.floor_natCast]
  exact hfactor p hp hpp t ht hprime a ha b hb hpa htb

theorem mixed_pair_residue_factorization (q : ℕ) (hq : 0 < q) (u v r s J : ℝ)
    (hr : ∀ p ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, p.Prime → q < p)
    (F : ℕ → ℕ → ℂ) (c : ℕ → ℕ → ℂ) (H : ℝ → ℝ → ℂ)
    (hfactor : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      ∀ t ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, t.Prime →
      ∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      Nat.ModEq q p a → Nat.ModEq q t b →
      F p t = c a b * H (Real.log p) (Real.log t)) :
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
        complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J
          (fun x => c a b * H x y)) := by
  rw [complexPrimeInterval_residues q hq r s hr]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← complexPrimeInterval_finset_sum]
  apply complexPrimeInterval_congr
  intro t ht hprime htb
  have ht0 : (0 : ℝ) < t := by exact_mod_cast hprime.pos
  rw [Real.exp_log ht0, Nat.floor_natCast, complexIntegerInterval_residues q hq u v J]
  apply Finset.sum_congr rfl
  intro a ha
  apply complexIntegerInterval_congr
  intro p hp hpa
  have hp0 : (0 : ℝ) < p :=
    (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
  rw [Real.exp_log hp0, Nat.floor_natCast]
  exact hfactor p hp t ht hprime a ha b hb hpa htb

end Ostmann

end OAI

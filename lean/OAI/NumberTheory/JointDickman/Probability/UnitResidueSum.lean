import OAI.NumberTheory.JointDickman.Analysis.CharacterResidues

namespace OAI

/-! # Summing a unit-supported weight against residue phases -/

namespace JointDickman

open Finset

open Classical in
theorem sum_unit_residues {q : ℕ} [NeZero q] (S : Finset ℕ)
    (f : ℕ → ℂ) (ψ : ZMod q → ℂ)
    (hunit : ∀ n ∈ S, f n ≠ 0 → IsUnit (n : ZMod q)) :
    ∑ n ∈ S, ψ (n : ZMod q) * f n =
      ∑ r : (ZMod q)ˣ, ψ r * ∑ n ∈ S, if (n : ZMod q) = r then f n else 0 := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases hf : f n = 0
  · simp [hf]
  obtain ⟨r, hr⟩ := hunit n hn hf
  rw [← hr]
  symm
  rw [sum_eq_single r]
  · simp
  · intro s _ hsr
    have hne : (r : ZMod q) ≠ s := fun h => hsr (Units.val_injective h.symm)
    simp [hne]
  · simp

open Classical in
theorem sum_unit_residue_error {q : ℕ} [NeZero q] (S : Finset ℕ)
    (f : ℕ → ℂ) (ψ : ZMod q → ℂ) (I : ℂ) {E : ℝ}
    (hunit : ∀ n ∈ S, f n ≠ 0 → IsUnit (n : ZMod q))
    (hψ : ∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1)
    (hE : ∀ r : (ZMod q)ˣ,
      ‖(∑ n ∈ S, if (n : ZMod q) = r then f n else 0) - I‖ ≤ E) :
    ‖(∑ n ∈ S, ψ (n : ZMod q) * f n) - (∑ r : (ZMod q)ˣ, ψ r) * I‖ ≤
      q.totient * E := by
  rw [sum_unit_residues S f ψ hunit, sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ r : (ZMod q)ˣ,
        ‖ψ r * (∑ n ∈ S, if (n : ZMod q) = r then f n else 0) - ψ r * I‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : (ZMod q)ˣ, E := by
      apply sum_le_sum
      intro r _
      rw [← mul_sub, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hψ r) (norm_nonneg _)).trans
        (by simpa using hE r)
    _ = _ := by simp [ZMod.card_units_eq_totient]

end JointDickman

end OAI

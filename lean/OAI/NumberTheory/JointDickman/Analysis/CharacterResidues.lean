import OAI.NumberTheory.JointDickman.Analysis.CharacterAuxiliaryBound
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! # Character orthogonality for the actual rough coefficients -/

namespace JointDickman

open Finset

noncomputable def progressionSum {q : ℕ} (S : Finset ℕ) (w : ℕ → ℝ)
    (r : ZMod q) : ℝ := ∑ n ∈ S, if (n : ZMod q) = r then w n else 0

open Classical in
theorem progressionSum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ) * (progressionSum S w (r : ZMod q) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ) *
        ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
  rw [progressionSum, Complex.ofReal_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = (w n : ℂ) * (if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = (w n : ℂ) * ∑ χ : DirichletCharacter ℂ q,
        χ (r⁻¹ : (ZMod q)ˣ) * χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit, ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

open Classical in
/-- The normalized character average loses no factor depending on the modulus. -/
theorem progressionSum_error_le {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) {E : ℝ} (hE : 0 ≤ E)
    (hunit : ∀ n ∈ S, w n ≠ 0 → IsUnit (n : ZMod q))
    (hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤ E) :
    |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| ≤ E := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hprincipal : (∑ n ∈ S, (w n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q)) =
      (∑ n ∈ S, w n : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    by_cases hw : w n = 0
    · simp [hw]
    · rw [MulChar.one_apply (hunit n hn hw), mul_one]
  have hid : (q.totient : ℂ) *
      ((progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
    have hφ0 : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    rw [mul_sub, mul_div_cancel₀ _ hφ0, progressionSum_characters]
    rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ q)), hprincipal,
      MulChar.one_apply_coe, one_mul, add_sub_cancel_right]
  have hsum : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤
      (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E := by
        apply sum_le_sum
        intro χ hχ
        rw [norm_mul, χ.unit_norm_eq_one, one_mul]
        exact hbound χ (ne_of_mem_erase hχ)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hE)
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [← hid, norm_mul, Complex.norm_natCast] at hsum
  have heq : ‖(progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)‖ =
      |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at hsum
  exact (mul_le_mul_iff_right₀ hφ).mp hsum

theorem roughSquarefreeWeight_coprime {P q n : ℕ} (hq : q ≠ 0) (hqP : q ≤ P)
    (z : ℝ) (hn : roughSquarefreeWeight (Nat.primesLE P) z n ≠ 0) : n.Coprime q := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hd : Disjoint n.primeFactors (Nat.primesLE P) := by
    by_contra h
    simp [roughSquarefreeWeight, h] at hn
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq).trans hqP, hp⟩)

end JointDickman

end OAI

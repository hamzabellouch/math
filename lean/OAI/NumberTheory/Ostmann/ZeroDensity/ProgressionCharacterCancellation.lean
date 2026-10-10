import Mathlib.Algebra.Group.Units.Equiv
import OAI.NumberTheory.Ostmann.Characters.PeriodicCharacterSum
import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # Exact cancellation of distinct short characters on a fixed progression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem complex_periodic_blocks (f : ℕ → ℂ) (q : ℕ)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (k r : ℕ) : ∑ a ∈ Finset.range (k * q + r), f a = ∑ a ∈ Finset.range r, f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q + r = q + (k * q + r) by ring, Finset.sum_range_add, hz, zero_add]
    have hp' (a : ℕ) : f (q + a) = f a := by simpa only [Nat.add_comm] using hp a
    simpa only [hp'] using ih

theorem complex_periodic_zero_sum_bound (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (hb : ∀ a, ‖f a‖ ≤ 1) (N : ℕ) : ‖∑ a ∈ Finset.range N, f a‖ ≤ q := by
  have he : N / q * q + N % q = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  rw [← he, complex_periodic_blocks f q hp hz]
  calc
    _ ≤ ∑ a ∈ Finset.range (N % q), ‖f a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
    _ = (N % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le

theorem sum_range_residues {M : ℕ} [NeZero M] (F : ZMod M → ℂ) :
    (∑ a ∈ Finset.range M, F (a : ZMod M)) = ∑ a : ZMod M, F a := by
  have he := (ZMod.finEquiv M).toEquiv.sum_comp F
  have hval (a : Fin M) : (ZMod.finEquiv M).toEquiv a = (a.val : ZMod M) := by
    cases M with
    | zero => exact Fin.elim0 a
    | succ M =>
      apply Fin.ext
      exact (Nat.mod_eq_of_lt a.isLt).symm
  simp_rw [hval] at he
  exact (Fin.sum_univ_eq_sum_range (fun a => F (a : ZMod M)) M).symm.trans he

noncomputable def characterPairValue {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (x : ZMod (q * r)) : ℂ :=
  χ ((ZMod.chineseRemainder hqr x).1) * conj (ψ ((ZMod.chineseRemainder hqr x).2))

theorem characterPairValue_nat {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (a : ℕ) :
    characterPairValue hqr χ ψ (a : ZMod (q * r)) = χ (a : ZMod q) * conj (ψ (a : ZMod r)) := by
  simp only [characterPairValue, map_natCast, Prod.fst_natCast, Prod.snd_natCast]

theorem characterPairValue_sum_zero {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) : (∑ x : ZMod (q * r), characterPairValue hqr χ ψ x) = 0 := by
  have he := (ZMod.chineseRemainder hqr).toEquiv.sum_comp
    (fun x : ZMod q × ZMod r => χ x.1 * conj (ψ x.2))
  change (∑ x, characterPairValue hqr χ ψ x) = _ at he
  rw [he, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

theorem characterPairValue_norm_le_one {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (x : ZMod (q * r)) :
    ‖characterPairValue hqr χ ψ x‖ ≤ 1 := by
  rw [characterPairValue, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (χ.norm_le_one _) (ψ.norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

/-- A step coprime to the two short moduli permutes the complete period.
This remains exact after fixing any residue class of the frequency modulus. -/
theorem character_progression_sum_bound {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (hM : M.Coprime (q * r)) :
    ‖∑ j ∈ Finset.range N, χ ((a + M * j : ℕ) : ZMod q) *
      conj (ψ ((a + M * j : ℕ) : ZMod r))‖ ≤ q * r := by
  let F := characterPairValue hqr χ ψ
  let f : ℕ → ℂ := fun j => F ((a + M * j : ℕ) : ZMod (q * r))
  have hp : Function.Periodic f (q * r) := by
    intro j
    simp only [f, Nat.cast_add, Nat.cast_mul]
    congr 1
    simp only [mul_add]
    have hz : ((q * r : ℕ) : ZMod (q * r)) = 0 := ZMod.natCast_self _
    simp only [Nat.cast_mul] at hz
    rw [hz, mul_zero, add_zero]
  have hz : (∑ j ∈ Finset.range (q * r), f j) = 0 := by
    have : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
    let e := (ZMod.unitOfCoprime M hM).mulLeft.trans (Equiv.addLeft (a : ZMod (q * r)))
    have he := e.sum_comp F
    have hev (z : ZMod (q * r)) : e z = (a : ZMod (q * r)) + (M : ZMod (q * r)) * z := by
      simp [e, Equiv.trans_apply, ZMod.coe_unitOfCoprime]
    simp_rw [hev] at he
    simp only [f, Nat.cast_add, Nat.cast_mul]
    have hs := sum_range_residues (M := q * r)
      (fun z => F ((a : ZMod (q * r)) + (M : ZMod (q * r)) * z))
    exact (hs.trans he).trans (characterPairValue_sum_zero hqr χ ψ hχ)
  have hb := complex_periodic_zero_sum_bound f (q * r)
    (Nat.mul_pos (NeZero.pos q) (NeZero.pos r)) hp hz
    (fun j => characterPairValue_norm_le_one hqr χ ψ _) N
  simpa only [f, F, characterPairValue_nat, Nat.cast_mul] using hb

theorem weighted_character_progression_bound {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (hM : M.Coprime (q * r)) (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j * (χ ((a + M * j : ℕ) : ZMod q) *
      conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤ discreteVariation w N * (q * r) := by
  apply weighted_sum_le_variation
  intro n _
  exact character_progression_sum_bound hqr χ ψ hχ a M n hM

/-- Sum the exact progression bounds over all interval/residue pieces.
The total variation budget includes the reciprocal-integer weight. -/
theorem character_interval_pieces_bound {I : Type*} [Fintype I]
    {q r : ℕ} [NeZero q] [NeZero r] (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hχ : χ ≠ 1)
    (a M N : I → ℕ) (hM : ∀ i, (M i).Coprime (q * r))
    (w : I → ℕ → ℂ) (V : ℝ) (hvar : ∑ i, discreteVariation (w i) (N i) ≤ V) :
    ‖∑ i, ∑ j ∈ Finset.range (N i), w i j *
      (χ ((a i + M i * j : ℕ) : ZMod q) * conj (ψ ((a i + M i * j : ℕ) : ZMod r)))‖ ≤
      V * (q * r) := by
  calc
    _ ≤ ∑ i, ‖∑ j ∈ Finset.range (N i), w i j *
      (χ ((a i + M i * j : ℕ) : ZMod q) * conj (ψ ((a i + M i * j : ℕ) : ZMod r)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, discreteVariation (w i) (N i) * (q * r) :=
      Finset.sum_le_sum (fun i _ => weighted_character_progression_bound hqr χ ψ hχ
        (a i) (M i) (N i) (hM i) (w i))
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hvar (by positivity)

end Ostmann

end OAI

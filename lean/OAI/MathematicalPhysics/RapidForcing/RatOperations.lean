import OAI.MathematicalPhysics.RapidForcing.RatComputable
import OAI.MathematicalPhysics.RapidForcing.ComputableAutomation

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

lemma rat_divInt_graph (n d : ℤ) (q : ℚ) (hd : d ≠ 0) :
    q.num * d = n * (q.den : ℤ) ↔ q = (n : ℚ) / d := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  conv_rhs => rw [← Rat.num_div_den q, div_eq_div_iff hq hd']
  exact_mod_cast (Iff.rfl : q.num * d = n * (q.den : ℤ) ↔ _)

@[fun_prop] lemma computable_rat_divInt : Computable (fun p : ℤ × ℤ => (p.1 : ℚ) / p.2) := by
  apply computable_of_graph _ (fun p q =>
      if p.2 = 0 then q = 0 else q.num * p.2 = p.1 * (q.den : ℤ))
  · have hi : PrimrecPred (fun p : (ℤ × ℤ) × ℚ =>
        (p.1.2 = 0 ∧ p.2 = 0) ∨ (p.1.2 ≠ 0 ∧ p.2.num * p.1.2 = p.1.1 * (p.2.den : ℤ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro p q
    split_ifs with hd
    · simp [hd]
    · exact rat_divInt_graph _ _ _ hd

@[fun_prop] lemma computable_rat_inv : Computable (fun q : ℚ => q⁻¹) := by
  have := computable_rat_divInt.comp (show Computable (fun q : ℚ => ((q.den : ℤ), q.num)) by fun_prop)
  exact this.of_eq (fun q => by simpa [Int.cast_natCast, inv_div] using congrArg Inv.inv (Rat.num_div_den q))

@[fun_prop] lemma computable_rat_div : Computable (fun p : ℚ × ℚ => p.1 / p.2) := by
  simpa [div_eq_mul_inv] using (show Computable (fun p : ℚ × ℚ => p.1 * p.2⁻¹) by fun_prop)

@[fun_prop] lemma computable_rat_abs : Computable (fun q : ℚ => |q|) := by
  apply Computable.of_eq (show Computable (fun q : ℚ => if 0 ≤ q then q else -q) by fun_prop)
  intro q
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

@[fun_prop] lemma computable_rat_max : Computable (fun p : ℚ × ℚ => max p.1 p.2) := by
  simpa only [max_def] using (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.2 else p.1) by fun_prop)

@[fun_prop] lemma computable_rat_pow : Computable (fun p : ℚ × ℕ => p.1 ^ p.2) := by
  have h := Computable.nat_rec (f := fun p : ℚ × ℕ => p.2)
    (g := fun _ => (1 : ℚ)) (h := fun p r => r.2 * p.1)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.2 <;> simp [pow_succ, *]

@[fun_prop] lemma computable_rat_natCeil : Computable (fun q : ℚ => ⌈q⌉₊) := by
  apply computable_of_compGraph _ (fun q n : _ =>
      if n = (0 : ℕ) then q ≤ 0 else (n - 1 : ℚ) < q ∧ q ≤ (n : ℚ))
  · have hi : CompPred (fun p : ℚ × ℕ =>
        (p.2 = 0 ∧ p.1 ≤ 0) ∨ (p.2 ≠ 0 ∧ (p.2 - 1 : ℚ) < p.1 ∧ p.1 ≤ (p.2 : ℚ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro q n
    by_cases hn : n = 0
    · simp [hn, eq_comm, Nat.ceil_eq_zero]
    · simp only [ite_eq_right hn]
      rw [eq_comm, Nat.ceil_eq_iff hn]
      simp only [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]

@[fun_prop] lemma computable_rat_natFloor : Computable (fun q : ℚ => ⌊q⌋₊) := by
  apply computable_of_compGraph _ (fun q n : _ =>
      if n = (0 : ℕ) then q < 1 else (n : ℚ) ≤ q ∧ q < (n : ℚ) + 1)
  · have hi : CompPred (fun p : ℚ × ℕ =>
        (p.2 = 0 ∧ p.1 < 1) ∨ (p.2 ≠ 0 ∧ (p.2 : ℚ) ≤ p.1 ∧ p.1 < (p.2 : ℚ) + 1)) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro q n
    by_cases hn : n = 0
    · simp [hn, eq_comm, Nat.floor_eq_zero]
    · simp only [ite_eq_right hn]
      rw [eq_comm, Nat.floor_eq_iff' hn]

end RapidForcing.EffectiveArithmetic

end

end OAI

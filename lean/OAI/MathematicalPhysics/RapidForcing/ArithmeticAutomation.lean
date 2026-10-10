import OAI.MathematicalPhysics.RapidForcing.IntegerPrimrec

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Primrec PrimrecPred Computable
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.fst Primrec.snd
  Primrec.pair Primrec.encode Primrec.decode Primrec.option_some Primrec.unpair
  Primrec.succ Primrec.pred Primrec.ite PrimrecPred.comp PrimrecPred.not PrimrecPred.and
  PrimrecPred.or Computable.id Computable.const Computable.comp Computable.fst Computable.snd
  Computable.pair Computable.encode Computable.decode Computable.option_some
attribute [fun_prop] primrec_int_ofNat primrec_int_negSucc primrec_int_natAbs
  primrec_int_toNat primrec_int_neg

@[fun_prop] lemma primrec_int_cast : Primrec (fun n : ℕ => (n : ℤ)) := primrec_int_ofNat

@[fun_prop] lemma primrec_nat_add : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add
@[fun_prop] lemma primrec_nat_sub : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub
@[fun_prop] lemma primrec_nat_mul : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul
@[fun_prop] lemma primrec_nat_div : Primrec (fun p : ℕ × ℕ => p.1 / p.2) := Primrec.nat_div
@[fun_prop] lemma primrec_nat_mod : Primrec (fun p : ℕ × ℕ => p.1 % p.2) := Primrec.nat_mod
@[fun_prop] lemma primrec_nat_max : Primrec (fun p : ℕ × ℕ => max p.1 p.2) := Primrec.nat_max
@[fun_prop] lemma primrec_nat_min : Primrec (fun p : ℕ × ℕ => min p.1 p.2) := Primrec.nat_min
@[fun_prop] lemma primrec_nat_le : PrimrecPred (fun p : ℕ × ℕ => p.1 ≤ p.2) := Primrec.nat_le
@[fun_prop] lemma primrec_nat_lt : PrimrecPred (fun p : ℕ × ℕ => p.1 < p.2) := Primrec.nat_lt
@[fun_prop] lemma primrec_eq {A : Type} [Primcodable A] :
    PrimrecPred (fun p : A × A => p.1 = p.2) := Primrec.eq

@[fun_prop] lemma primrec_nat_pow : Primrec (fun p : ℕ × ℕ => p.1 ^ p.2) := by
  have h := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => 1) (h := fun p r => r.2 * p.1)
    (by fun_prop) (by fun_prop) (by unfold Primrec₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih]

@[fun_prop] lemma primrec_factorial : Primrec Nat.factorial := by
  exact (Primrec.nat_rec' Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
        (fun n => by
          change Nat.rec 1 (fun j IH => (j + 1) * IH) n = n.factorial
          induction n <;> simp [Nat.factorial, *])

@[fun_prop] lemma primrec_int_subNat : Primrec (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) := by
  have h : Primrec (fun p : ℕ × ℕ => if p.2 ≤ p.1 then Int.ofNat (p.1 - p.2)
      else - Int.ofNat (p.2 - p.1)) := by fun_prop
  exact h.of_eq (fun p => by split_ifs <;>
    simp only [Int.ofNat_eq_natCast] <;> omega)

lemma int_difference_parts (z : ℤ) : (z.toNat : ℤ) - (-z).toNat = z := by omega

@[fun_prop] lemma primrec_int_add : Primrec (fun p : ℤ × ℤ => p.1 + p.2) := by
  have h : Primrec (fun p : ℤ × ℤ =>
      ((p.1.toNat + p.2.toNat : ℕ) : ℤ) - ((-p.1).toNat + (-p.2).toNat : ℕ)) :=
    primrec_int_subNat.comp (show Primrec (fun p : ℤ × ℤ =>
      (p.1.toNat + p.2.toNat, (-p.1).toNat + (-p.2).toNat)) by fun_prop)
  exact h.of_eq (fun p => by omega)

@[fun_prop] lemma primrec_int_sub : Primrec (fun p : ℤ × ℤ => p.1 - p.2) := by
  simpa [sub_eq_add_neg] using (show Primrec (fun p : ℤ × ℤ => p.1 + -p.2) by fun_prop)

@[fun_prop] lemma primrec_int_mul : Primrec (fun p : ℤ × ℤ => p.1 * p.2) := by
  have h : Primrec (fun p : ℤ × ℤ =>
    ((p.1.toNat * p.2.toNat + (-p.1).toNat * (-p.2).toNat : ℕ) : ℤ) -
      ((p.1.toNat * (-p.2).toNat + (-p.1).toNat * p.2.toNat : ℕ) : ℤ)) := by fun_prop
  apply h.of_eq
  intro p
  push_cast
  conv_rhs => rw [← int_difference_parts p.1, ← int_difference_parts p.2]
  ring

@[fun_prop] lemma primrec_int_le : PrimrecPred (fun p : ℤ × ℤ => p.1 ≤ p.2) := by
  have h : PrimrecPred (fun p : ℤ × ℤ =>
    p.1.toNat + (-p.2).toNat ≤ p.2.toNat + (-p.1).toNat) := by fun_prop
  exact h.of_eq (fun p => by omega)

@[fun_prop] lemma primrec_int_lt : PrimrecPred (fun p : ℤ × ℤ => p.1 < p.2) := by
  exact (PrimrecPred.not (primrec_int_le.comp (Primrec.snd.pair Primrec.fst))).of_eq
    (fun p => not_le)

@[fun_prop] lemma primrec_nat_gcd : Primrec (fun p : ℕ × ℕ => p.1.gcd p.2) := by
  have h : Primrec (fun p : ℕ × ℕ => Nat.findGreatest (fun k => p.1 % k = 0 ∧ p.2 % k = 0)
      (p.1 + p.2)) := by
    apply Primrec.nat_findGreatest (by fun_prop)
    unfold PrimrecRel
    fun_prop
  apply h.of_eq
  rintro ⟨m, n⟩
  by_cases hmn : m + n = 0
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst m; subst n; rfl
  have hg : m.gcd n ≤ m + n := by
    by_cases hm : 0 < m
    · exact (Nat.gcd_le_left n hm).trans (Nat.le_add_right _ _)
    · have hn : 0 < n := by omega
      exact (Nat.gcd_le_right m hn).trans (Nat.le_add_left _ _)
  have hgpos : 0 < m.gcd n := by
    by_cases hm : 0 < m
    · exact Nat.gcd_pos_of_pos_left n hm
    · exact Nat.gcd_pos_of_pos_right m (by omega)
  have hd : ∀ k, m % k = 0 ∧ n % k = 0 ↔ k ∣ m.gcd n := by
    intro k
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_gcd_iff]
  apply le_antisymm
  · have hs := Nat.findGreatest_spec (P := fun k => m % k = 0 ∧ n % k = 0) hg ((hd _).mpr (dvd_refl _))
    exact Nat.le_of_dvd hgpos ((hd _).mp hs)
  · exact Nat.le_findGreatest hg ((hd _).mpr (dvd_refl _))

end RapidForcing.EffectiveArithmetic

end

end OAI

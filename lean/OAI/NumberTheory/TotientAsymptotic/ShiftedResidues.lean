import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveCRT
import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveModel

namespace OAI

/-! Identifying finite congruence counts with the exact CRT root count. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedRootCount_eq_count (d b : ℕ) (hd : 0 < d) :
    shiftedRootCount d b = Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let e : {q : ℕ // q<d ∧ d ∣ shiftedSievePolynomial b q} ≃
      {r : ZMod d // r*((b:ZMod d)*r+1)=0} := {
    toFun := fun q => ⟨q.val,by
      have hh := (ZMod.natCast_eq_zero_iff (shiftedSievePolynomial b q.val) d).mpr q.property.2
      simpa only [shiftedSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt r.val,by
      apply (ZMod.natCast_eq_zero_iff (shiftedSievePolynomial b r.val.val) d).mp
      simpa only [shiftedSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        ZMod.natCast_zmod_val] using r.property⟩
    left_inv := fun q => by
      apply Subtype.ext
      exact ZMod.val_natCast_of_lt q.property.1
    right_inv := fun r => by
      apply Subtype.ext
      exact ZMod.natCast_zmod_val r.val }
  let _ : Fintype {q : ℕ // q<d ∧ d ∣ shiftedSievePolynomial b q} :=
    Nat.CountSet.fintype (fun q => d ∣ shiftedSievePolynomial b q) d
  rw [Nat.count_eq_card_fintype]
  exact (Nat.card_congr e).symm.trans Nat.card_eq_fintype_card

lemma shiftedRootCount_one (b : ℕ) : shiftedRootCount 1 b = 1 := by
  rw [shiftedRootCount_eq_count 1 b (by norm_num),Nat.count_one]
  simp [shiftedSievePolynomial]

end TotientAsymptotic

end

end OAI

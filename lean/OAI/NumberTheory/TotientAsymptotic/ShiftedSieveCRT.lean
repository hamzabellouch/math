import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveRoots

namespace OAI

/-! Multiplication of the exact shifted-prime residue counts by the Chinese remainder theorem. -/
noncomputable section
namespace TotientAsymptotic

def shiftedRootCount (d b : ℕ) : ℕ :=
  Nat.card {r : ZMod d // r*((b:ZMod d)*r+1)=0}

lemma shiftedRootCount_eq_card (d b : ℕ) [NeZero d] :
    shiftedRootCount d b = (shiftedSieveRoots d b).card := by
  rw [shiftedRootCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

lemma shiftedRootCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (b : ℕ) :
    shiftedRootCount (m*n) b = shiftedRootCount m b*shiftedRootCount n b := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero n := ⟨hn⟩
  let e := ZMod.chineseRemainder hcop
  have he (r : ZMod (m*n)) : r*((b:ZMod (m*n))*r+1)=0 ↔
      (e r).1*((b:ZMod m)*(e r).1+1)=0 ∧ (e r).2*((b:ZMod n)*(e r).2+1)=0 := by
    calc
      _ ↔ e (r*((b:ZMod (m*n))*r+1))=0 := e.map_eq_zero_iff.symm
      _ ↔ _ := by
        simp only [map_mul,map_add,map_natCast,map_one,Prod.ext_iff]
        rfl
  let ep : {r : ZMod (m*n) // r*((b:ZMod (m*n))*r+1)=0} ≃
      {r : ZMod m × ZMod n //
        r.1*((b:ZMod m)*r.1+1)=0 ∧ r.2*((b:ZMod n)*r.2+1)=0} :=
    e.toEquiv.subtypeEquiv he
  let ee := ep.trans (Equiv.subtypeProdEquivProd
    (p := fun r : ZMod m => r*((b:ZMod m)*r+1)=0)
    (q := fun r : ZMod n => r*((b:ZMod n)*r+1)=0))
  unfold shiftedRootCount
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact (Fintype.card_congr ee).trans (Fintype.card_prod _ _)

lemma shiftedRootCount_prime (p b : ℕ) [Fact p.Prime] :
    shiftedRootCount p b = if p ∣ b then 1 else 2 := by
  rw [shiftedRootCount_eq_card,shiftedSieveRoots_card]

end TotientAsymptotic

end

end OAI

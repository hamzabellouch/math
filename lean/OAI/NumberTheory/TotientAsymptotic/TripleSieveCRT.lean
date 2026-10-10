import OAI.NumberTheory.TotientAsymptotic.TripleSieveRoots
import OAI.NumberTheory.TotientAsymptotic.PeriodicSieveCount

namespace OAI

/-! Exact CRT and interval discrepancies for the three-form collision sieve. -/
noncomputable section
namespace TotientAsymptotic

def tripleSievePolynomial (a b q : ℕ) : ℕ := q*(a*q+1)*(b*q+1)

def tripleRootCount (d a b : ℕ) : ℕ :=
  Nat.card {r : ZMod d // r*((a:ZMod d)*r+1)*((b:ZMod d)*r+1)=0}

lemma tripleRootCount_eq_card (d a b : ℕ) [NeZero d] :
    tripleRootCount d a b = (tripleSieveRoots d a b).card := by
  rw [tripleRootCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

lemma tripleRootCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (a b : ℕ) :
    tripleRootCount (m*n) a b = tripleRootCount m a b*tripleRootCount n a b := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero n := ⟨hn⟩
  let e := ZMod.chineseRemainder hcop
  have he (r : ZMod (m*n)) : r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1)=0 ↔
      (e r).1*((a:ZMod m)*(e r).1+1)*((b:ZMod m)*(e r).1+1)=0 ∧
      (e r).2*((a:ZMod n)*(e r).2+1)*((b:ZMod n)*(e r).2+1)=0 := by
    calc
      _ ↔ e (r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1))=0 := e.map_eq_zero_iff.symm
      _ ↔ _ := by
        simp only [map_mul,map_add,map_natCast,map_one,Prod.ext_iff]
        rfl
  let ep : {r : ZMod (m*n) // r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1)=0} ≃
      {r : ZMod m × ZMod n //
        r.1*((a:ZMod m)*r.1+1)*((b:ZMod m)*r.1+1)=0 ∧
        r.2*((a:ZMod n)*r.2+1)*((b:ZMod n)*r.2+1)=0} :=
    e.toEquiv.subtypeEquiv he
  let ee := ep.trans (Equiv.subtypeProdEquivProd
    (p := fun r : ZMod m => r*((a:ZMod m)*r+1)*((b:ZMod m)*r+1)=0)
    (q := fun r : ZMod n => r*((a:ZMod n)*r+1)*((b:ZMod n)*r+1)=0))
  unfold tripleRootCount
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact (Fintype.card_congr ee).trans (Fintype.card_prod _ _)

lemma tripleRootCount_eq_count (d a b : ℕ) (hd : 0 < d) :
    tripleRootCount d a b = Nat.count (fun q => d ∣ tripleSievePolynomial a b q) d := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let e : {q : ℕ // q<d ∧ d ∣ tripleSievePolynomial a b q} ≃
      {r : ZMod d // r*((a:ZMod d)*r+1)*((b:ZMod d)*r+1)=0} := {
    toFun := fun q => ⟨q.val,by
      have hh := (ZMod.natCast_eq_zero_iff (tripleSievePolynomial a b q.val) d).mpr q.property.2
      simpa only [tripleSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh⟩
    invFun := fun r => ⟨r.val.val,ZMod.val_lt r.val,by
      apply (ZMod.natCast_eq_zero_iff (tripleSievePolynomial a b r.val.val) d).mp
      simpa only [tripleSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        ZMod.natCast_zmod_val] using r.property⟩
    left_inv := fun q => by apply Subtype.ext; exact ZMod.val_natCast_of_lt q.property.1
    right_inv := fun r => by apply Subtype.ext; exact ZMod.natCast_zmod_val r.val }
  let _ : Fintype {q : ℕ // q<d ∧ d ∣ tripleSievePolynomial a b q} :=
    Nat.CountSet.fintype (fun q => d ∣ tripleSievePolynomial a b q) d
  rw [Nat.count_eq_card_fintype]
  exact (Nat.card_congr e).symm.trans Nat.card_eq_fintype_card

lemma tripleSievePolynomial_mod (a b d q : ℕ) :
    tripleSievePolynomial a b q % d = tripleSievePolynomial a b (q%d) % d := by
  simp [tripleSievePolynomial,Nat.add_mod,Nat.mul_mod]

lemma tripleSieve_count_error (a b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(Nat.count (fun q => d ∣ tripleSievePolynomial a b q) N:ℝ)-
      (N:ℝ)/d*(tripleRootCount d a b:ℝ)| ≤ d := by
  rw [tripleRootCount_eq_count d a b hd]
  apply count_periodic_error d hd
  intro q
  simp only [Nat.dvd_iff_mod_eq_zero,tripleSievePolynomial_mod a b d q]

end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.TotientAsymptotic.ActualFordData

namespace OAI

/-! Prime and smoothness bounds for all the choices in the class partition. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma wholeWitnessPrime_prime {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p j : ℕ} (hp : p.Prime) (hj : j ≤ L x H) :
    (wholeWitnessPrime p η j).Prime := by
  by_cases hz : j=0
  · simpa [wholeWitnessPrime,hz] using hp
  · simpa only [wholeWitnessPrime,ite_eq_right hz] using
      (hη.2.1 j (Finset.mem_Icc.mpr ⟨by omega,hj⟩)).1

lemma witnessBlockValue_pos {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p i k : ℕ} (hp : p.Prime) (hk : k ≤ L x H) :
    0 < witnessBlockValue p η i k := by
  apply Nat.mul_pos (Nat.totient_pos.mpr (suffixPreimage_pos hη))
  apply Finset.prod_pos
  intro j hj
  exact Nat.sub_pos_of_lt (wholeWitnessPrime_prime hη hp ((Finset.mem_Icc.mp hj).2.trans hk)).one_lt

lemma whole_shift_le_block {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p i k j : ℕ} (hp : p.Prime) (hk : k ≤ L x H)
    (hj : j ∈ Finset.Icc i k) :
    wholeWitnessPrime p η j-1 ≤ witnessBlockValue p η i k := by
  apply Nat.le_of_dvd (witnessBlockValue_pos hη hp hk)
  change wholeWitnessPrime p η j-1 ∣
    (suffixPreimage η k).totient*∏ r ∈ Finset.Icc i k, (wholeWitnessPrime p η r-1)
  exact (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime p η r-1) hj).trans (dvd_mul_left _ _)

lemma canceledPrimesAt_prime_bound {x t y : ℝ} {H i : ℕ}
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : GoodCollisionBlock x t H i y q) (I : Finset ℕ)
    (hk : collisionLastIndex x i ≤ L x H) :
    ∀ j, (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j).Prime ∧
      (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j : ℝ) ≤ y+1 := by
  intro j
  have hj := (canceledIndices i (collisionLastIndex x i) I).orderEmbOfFin_mem rfl j
  have hj' := (Finset.mem_sdiff.mp hj).1
  have hη := (chosenRemainder_spec hq.left.1.2.2.1).1
  have hprime := wholeWitnessPrime_prime hη hq.left.1.1 ((Finset.mem_Icc.mp hj').2.trans hk)
  refine ⟨hprime,?_⟩
  have hle := whole_shift_le_block hη hq.left.1.1 hk hj'
  have hler : ((canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ) : ℝ) ≤ y :=
    (show ((canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ) : ℝ) ≤
      witnessBlockValue q.1.head (chosenRemainder x H q.1.tail) i (collisionLastIndex x i) by exact_mod_cast hle).trans hq.size
  have he : (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j : ℝ)=
      (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ)+1 := by
    exact_mod_cast (Nat.sub_add_cancel hprime.one_lt.le).symm
  linarith

end TotientAsymptotic

end

end OAI

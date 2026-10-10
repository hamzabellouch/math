import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveRoots

namespace OAI

/-! The local three-linear-form sieve in Ford's collision argument. -/
noncomputable section
namespace TotientAsymptotic

def tripleSieveRoots (p a b : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun r => r*((a:ZMod p)*r+1)*((b:ZMod p)*r+1)=0)

lemma tripleSieveRoots_eq_union (p a b : ℕ) [Fact p.Prime] :
    tripleSieveRoots p a b = shiftedSieveRoots p a ∪ shiftedSieveRoots p b := by
  ext r
  simp only [tripleSieveRoots,shiftedSieveRoots,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union,mul_eq_zero]
  tauto

lemma zero_mem_tripleSieveRoots (p a b : ℕ) [NeZero p] :
    (0:ZMod p) ∈ tripleSieveRoots p a b := by simp [tripleSieveRoots]

lemma tripleSieveRoots_card_le (p a b : ℕ) [Fact p.Prime] :
    (tripleSieveRoots p a b).card ≤ 3 := by
  have hcard := Finset.card_union_add_card_inter (shiftedSieveRoots p a) (shiftedSieveRoots p b)
  have hint : 1 ≤ (shiftedSieveRoots p a ∩ shiftedSieveRoots p b).card := by
    apply Finset.card_pos.mpr
    exact ⟨0,by simp [shiftedSieveRoots]⟩
  rw [shiftedSieveRoots_card,shiftedSieveRoots_card] at hcard
  rw [tripleSieveRoots_eq_union]
  split_ifs at hcard <;> omega

lemma tripleSieveRoots_card_eq_three (p a b : ℕ) [Fact p.Prime]
    (ha : ¬p ∣ a) (hb : ¬p ∣ b) (hab : (a:ZMod p) ≠ b) :
    (tripleSieveRoots p a b).card = 3 := by
  have ha0 : (a:ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff a p).not.mpr ha
  have hb0 : (b:ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hb
  have hinv : -(a:ZMod p)⁻¹ ≠ -(b:ZMod p)⁻¹ := by
    intro h
    apply hab
    exact inv_injective (neg_injective h)
  rw [tripleSieveRoots_eq_union,shiftedSieveRoots_of_not_dvd p a ha,
    shiftedSieveRoots_of_not_dvd p b hb]
  have he : ({0,-(a:ZMod p)⁻¹} ∪ {0,-(b:ZMod p)⁻¹} : Finset (ZMod p)) =
      {0,-(a:ZMod p)⁻¹,-(b:ZMod p)⁻¹} := by ext r; simp
  rw [he]
  simp [Finset.card_insert_of_notMem,ha0,hb0,hinv]

end TotientAsymptotic

end

end OAI

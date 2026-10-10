import OAI.NumberTheory.TotientAsymptotic.PublishedComparison

namespace OAI

/-! Local sieve densities for a prime q with b*q+1 also prime. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def shiftedSieveRoots (p b : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun r => r*((b:ZMod p)*r+1)=0)

lemma shiftedSieveRoots_of_dvd (p b : ℕ) [Fact p.Prime] (hpb : p ∣ b) :
    shiftedSieveRoots p b = {0} := by
  have hb : (b:ZMod p)=0 := by simpa only [ZMod.natCast_eq_zero_iff] using hpb
  ext r
  simp [shiftedSieveRoots,hb]

lemma shiftedSieveRoots_of_not_dvd (p b : ℕ) [Fact p.Prime] (hpb : ¬p ∣ b) :
    shiftedSieveRoots p b = {0,-(b:ZMod p)⁻¹} := by
  have hb : (b:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hpb
  have hlin (r : ZMod p) : (b:ZMod p)*r+1=0 ↔ r=-(b:ZMod p)⁻¹ := by
    constructor
    · intro hr
      apply mul_left_cancel₀ hb
      rw [mul_neg,mul_inv_cancel₀ hb]
      exact eq_neg_of_add_eq_zero_left hr
    · rintro rfl
      simp [hb]
  ext r
  simp [shiftedSieveRoots,mul_eq_zero,hlin]

lemma shiftedSieveRoots_card (p b : ℕ) [Fact p.Prime] :
    (shiftedSieveRoots p b).card = if p ∣ b then 1 else 2 := by
  by_cases hpb : p ∣ b
  · simp [shiftedSieveRoots_of_dvd p b hpb,hpb]
  · rw [shiftedSieveRoots_of_not_dvd p b hpb,ite_eq_right hpb]
    have hb : (b:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hpb
    exact Finset.card_pair (Ne.symm (neg_ne_zero.mpr (inv_ne_zero hb)))

lemma shiftedSieveRoots_mem_of_dvd (p b q : ℕ) [Fact p.Prime]
    (hq : p ∣ q*(b*q+1)) : (q:ZMod p) ∈ shiftedSieveRoots p b := by
  simp only [shiftedSieveRoots,Finset.mem_filter,Finset.mem_univ,true_and]
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using
    (ZMod.natCast_eq_zero_iff (q*(b*q+1)) p).mpr hq

end TotientAsymptotic

end

end OAI

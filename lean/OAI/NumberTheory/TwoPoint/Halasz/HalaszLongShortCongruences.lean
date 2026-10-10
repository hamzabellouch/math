import OAI.NumberTheory.TwoPoint.Halasz.HalaszCongruenceEnergy

namespace OAI

/-! The congruence energy bound for the actual long/short monomial system.
No abstract analytic input occurs in this finite counting step. -/
namespace TwoPointCorrelations

open Finset Polynomial
open scoped Classical

def halaszNatPowerFrequency {s N : ℕ} (k : ℕ) (x : Fin s → Fin N) : Fin k → ℕ :=
  fun j => ∑ i, ((x i).val+1)^(j.val+1)

def halaszLongShortFrequency {s k N Q : ℕ} (p q : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ℕ :=
  fun j => halaszNatPowerFrequency k x.1 j +
    (p*q)^(j.val+1)*halaszNatPowerFrequency k x.2 j

def halaszLongResidues {s k N Q : ℕ} (p r : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ZMod (p^(r+1)) :=
  fun i => ((x.1 i).val+1:ℕ)

lemma halasz_long_short_congruence {s k N Q : ℕ} (p q r : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) (j : Fin k) :
    (∑ i, ((X^(j.val+1) : (ZMod (p^(r+1)))[X]).eval
      (halaszLongResidues p r x i))).val % p^(min (j.val+1) (r+1)) =
        halaszLongShortFrequency p q x j % p^(min (j.val+1) (r+1)) := by
  have hcast : (∑ i, ((X^(j.val+1) : (ZMod (p^(r+1)))[X]).eval
      (halaszLongResidues p r x i))) =
      (halaszNatPowerFrequency k x.1 j : ZMod (p^(r+1))) := by
    simp only [eval_pow,eval_X,halaszLongResidues,halaszNatPowerFrequency,
      Nat.cast_sum,Nat.cast_pow]
  rw [hcast,ZMod.val_natCast,Nat.mod_mod_of_dvd _
    (pow_dvd_pow p (Nat.min_le_right _ _))]
  have hd : p^(min (j.val+1) (r+1)) ∣
      (p*q)^(j.val+1)*halaszNatPowerFrequency k x.2 j := by
    apply dvd_mul_of_dvd_left
    exact (pow_dvd_pow p (Nat.min_le_left _ _)).trans
      (by rw [mul_pow]; exact dvd_mul_right _ _)
  simp only [halaszLongShortFrequency,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,
    add_zero,Nat.mod_mod]

theorem halasz_long_short_congruence_energy {s k N Q p r : ℕ} [Fact p.Prime]
    (hkp : k<p) (hrk : r+1≤k) (q : ℕ)
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszLongShortFrequency p q) ≤
      (k^k*p^((r+1)*r/2)) * halaszFiberEnergy F
        (fun x => (halaszLongShortFrequency p q x,halaszLongResidues p r x)) := by
  apply halasz_mixed_congruence_energy_triangular hkp hrk
    (fun j => X^(j.val+1))
  · intro j
    exact natDegree_X_pow_le _
  · intro j
    simp
  · intro x hx
    simpa only [halaszLongResidues,map_natCast] using hF x hx
  · exact fun x _ j => halasz_long_short_congruence p q r x j

end TwoPointCorrelations

end OAI

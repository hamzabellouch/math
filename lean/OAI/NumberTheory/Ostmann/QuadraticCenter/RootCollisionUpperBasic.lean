import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Preliminaries
open scoped BigOperators

def rootMinShift (U : Finset ℕ) (hU : U.Nonempty) (a : U) : ℕ :=
  a.val - U.min' hU

theorem rootMinShift_injective (U : Finset ℕ) (hU : U.Nonempty) :
    Function.Injective (rootMinShift U hU) := by
  intro a b hab
  apply Subtype.ext
  have ha := U.min'_le a.val a.property
  have hb := U.min'_le b.val b.property
  dsimp [rootMinShift] at hab
  omega

theorem rootMinShift_image_card (U : Finset ℕ) (hU : U.Nonempty) :
    (Finset.univ.image (rootMinShift U hU)).card = U.card := by
  rw [Finset.card_image_of_injective _ (rootMinShift_injective U hU)]
  simp

theorem rootMinShift_congr_iff (U : Finset ℕ) (hU : U.Nonempty)
    (p : ℕ) (a b : U) :
    (rootMinShift U hU a : ZMod p) = (rootMinShift U hU b : ZMod p) ↔
      (a.val : ZMod p) = (b.val : ZMod p) := by
  simp only [rootMinShift, Nat.cast_sub (U.min'_le a.val a.property),
    Nat.cast_sub (U.min'_le b.val b.property), sub_left_inj]

theorem rootCollisionProbability_eq_shift (U : Finset ℕ) (hU : U.Nonempty) (p : ℕ) :
    rootCollisionProbability U p = congruenceCollisionEnergy p (rootMinShift U hU)
      (fun _ => (U.card:ℝ)⁻¹) := by
  simp only [rootCollisionProbability, congruenceCollisionEnergy, rootMinShift_congr_iff]

theorem rootCollisionProbability_weighted_le_diameter (U : Finset ℕ) (hU : U.Nonempty)
    (Q : ℕ) (D : ℝ) (hD : 1 ≤ D)
    (hdiam : ∀ a ∈ U, ∀ b ∈ U, |(a:ℝ)-b| ≤ D) :
    (∑ p ∈ Q.primesLE, Real.log p * rootCollisionProbability U p) ≤
      Real.log (⌈D⌉₊:ℕ) + Real.log 4 * Q / U.card := by
  have hceil : 1 ≤ ⌈D⌉₊ := by
    have hc : (1:ℝ) ≤ (⌈D⌉₊:ℕ) := hD.trans (Nat.le_ceil D)
    exact_mod_cast hc
  have hbound (a : U) : rootMinShift U hU a ≤ ⌈D⌉₊ := by
    have ha := U.min'_le a.val a.property
    have hd := hdiam a.val a.property (U.min' hU) (U.min'_mem hU)
    have hsub : (rootMinShift U hU a:ℝ) ≤ D := by
      dsimp [rootMinShift]
      rw [Nat.cast_sub ha]
      exact (le_abs_self _).trans hd
    exact_mod_cast hsub.trans (Nat.le_ceil D)
  have h := weighted_prime_collision_energy_le Q ⌈D⌉₊ (rootMinShift U hU)
    (fun _ => (U.card:ℝ)⁻¹) hceil (rootMinShift_injective U hU) hbound
    (by intro a; positivity) (rootUniformMass_sum U hU) (fun _ => le_rfl)
  simpa only [← rootCollisionProbability_eq_shift U hU, div_eq_mul_inv] using h

theorem log_ceil_le_log_add_log_two (D : ℝ) (hD : 1 ≤ D) :
    Real.log (⌈D⌉₊:ℕ) ≤ Real.log D + Real.log 2 := by
  have hDp : 0 < D := by linarith
  have hc : 0 < ((⌈D⌉₊:ℕ):ℝ) := hDp.trans_le (Nat.le_ceil D)
  have hb : ((⌈D⌉₊:ℕ):ℝ) ≤ 2*D := by
    have hh := Nat.ceil_lt_add_one hDp.le
    linarith
  calc
    _ ≤ Real.log (2*D) := Real.log_le_log hc hb
    _ = _ := by rw [Real.log_mul (by norm_num) hDp.ne']; ring

end Ostmann.QuadraticCenter

end

end OAI

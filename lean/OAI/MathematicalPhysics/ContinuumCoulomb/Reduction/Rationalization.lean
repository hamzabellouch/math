import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.FormStability

namespace OAI

/-!
# Rational nuclear output with a ground-energy error budget

Coordinate rounding controls the full Coulomb variational infimum while
retaining the nuclear charges, nuclei count and electron number.
-/

noncomputable section
namespace ContinuumCoulomb

/-- Rational nuclear data produced from real centers and integral charges. -/
def rationalizeNuclei {m : ℕ} (S : Coulomb.Nuclei m) (n : ℕ) (hn : 0 < n)
    (charge : Fin m → ℕ) (hcharge : ∀ a, (charge a : ℝ) = S.charge a)
    (denominator : ℕ) (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖) :
    NuclearData where
  nuclei := m
  nuclei_pos := S.nonempty
  position := fun a => roundPosition denominator (S.position a)
  distinct := roundPosition_injective hdenom S.position hsep
  charge := charge
  charge_pos := by
    intro a
    have h : (0 : ℝ) < (charge a : ℝ) := by
      rw [hcharge]
      exact lt_of_lt_of_le (by norm_num) (S.charge_ge_one a)
    exact_mod_cast h
  electrons := n
  electrons_pos := hn

theorem rationalizeNuclei_charge {m n denominator : ℕ} (S : Coulomb.Nuclei m)
    (hn : 0 < n) (charge : Fin m → ℕ) (hcharge : ∀ a, (charge a : ℝ) = S.charge a)
    (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖) :
    (rationalizeNuclei S n hn charge hcharge denominator hdenom hsep).toNuclei.charge =
      S.charge := by
  funext a
  exact hcharge a

theorem rationalizeNuclei_position_error {m n denominator : ℕ} (S : Coulomb.Nuclei m)
    (hn : 0 < n) (charge : Fin m → ℕ) (hcharge : ∀ a, (charge a : ℝ) = S.charge a)
    (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖)
    (a : Fin m) :
    ‖S.position a -
      (rationalizeNuclei S n hn charge hcharge denominator hdenom hsep).toNuclei.position a‖ ≤
        3 / (denominator : ℝ) := by
  rw [norm_sub_rev]
  exact roundPosition_error hdenom (S.position a)

/-- The rounded output has distinct rational positions and the same integer
charges, and its true fermionic bottom changes by at most the stated budget. -/
theorem rationalizeNuclei_groundEnergy_error {m n denominator : ℕ} (S : Coulomb.Nuclei m)
    (hn : 0 < n) (charge : Fin m → ℕ) (hcharge : ∀ a, (charge a : ℝ) = S.charge a)
    (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖)
    (trial : FormState n) (htrial : normSq trial = 1)
    (hsmall : 96 * Coulomb.totalCharge S / (denominator : ℝ) ≤ 1) :
    |(groundEnergy (rationalizeNuclei S n hn charge hcharge denominator hdenom hsep)).toReal -
      (formGroundEnergy S n).toReal| ≤
      96 * Coulomb.totalCharge S / (denominator : ℝ) *
        (Coulomb.form S trial.val + 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2) := by
  have hfactor : 32 * (3 / (denominator : ℝ)) * Coulomb.totalCharge S =
      96 * Coulomb.totalCharge S / (denominator : ℝ) := by ring
  rw [groundEnergy_eq_formGroundEnergy]
  change |(formGroundEnergy
      (rationalizeNuclei S n hn charge hcharge denominator hdenom hsep).toNuclei n).toReal -
        (formGroundEnergy S n).toReal| ≤ _
  have h := formGroundEnergy_position_stability_trial S
    (rationalizeNuclei S n hn charge hcharge denominator hdenom hsep).toNuclei
    trial htrial (by positivity : (0 : ℝ) ≤ 3 / (denominator : ℝ))
    (rationalizeNuclei_charge S hn charge hcharge hdenom hsep).symm
    (rationalizeNuclei_position_error S hn charge hcharge hdenom hsep)
    (by simpa only [hfactor] using hsmall)
  rw [hfactor] at h
  exact h

/-- In the unit-charge case the output uses the unit-charge input structure. -/
def rationalizeUnitNuclei {m : ℕ} (S : Coulomb.Nuclei m) (n : ℕ) (hn : 0 < n)
    (denominator : ℕ) (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖) :
    UnitNuclearData where
  nuclei := m
  nuclei_pos := S.nonempty
  position := fun a => roundPosition denominator (S.position a)
  distinct := roundPosition_injective hdenom S.position hsep
  electrons := n
  electrons_pos := hn

theorem rationalizeUnitNuclei_groundEnergy_error {m n denominator : ℕ} (S : Coulomb.Nuclei m)
    (hn : 0 < n) (hunit : ∀ a, S.charge a = 1) (hdenom : 0 < denominator)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖S.position i - S.position j‖)
    (trial : FormState n) (htrial : normSq trial = 1)
    (hsmall : 96 * Coulomb.totalCharge S / (denominator : ℝ) ≤ 1) :
    |(unitGroundEnergy (rationalizeUnitNuclei S n hn denominator hdenom hsep)).toReal -
      (formGroundEnergy S n).toReal| ≤
      96 * Coulomb.totalCharge S / (denominator : ℝ) *
        (Coulomb.form S trial.val + 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2) := by
  exact rationalizeNuclei_groundEnergy_error S hn (fun _ => 1)
    (fun a => by simpa using (hunit a).symm) hdenom hsep trial htrial hsmall

end ContinuumCoulomb

end

end OAI

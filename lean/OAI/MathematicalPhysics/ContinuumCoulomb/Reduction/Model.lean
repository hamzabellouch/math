import OAI.Analysis.CoulombRadii.FormDomain.Add

namespace OAI

/-!
# Full spinful continuum Coulomb energy

Nuclear data and electronic states use the weak H¹ domain and translated
Hardy bounds. Antisymmetry
permutes spin and position together. No orbital projection or spin sector is
imposed. The bottom takes values in `EReal` so its definition does not assume
existence of a normalized state or a minimizing eigenvector.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

abbrev Position := Coulomb.Space
abbrev Configuration := Coulomb.Configuration
abbrev SpinConfiguration := Coulomb.Spins

/-- Finite clamped-nucleus data for binary-encoded positive integer charges. -/
structure NuclearData where
  nuclei : ℕ
  nuclei_pos : 0 < nuclei
  position : Fin nuclei → Fin 3 → ℚ
  distinct : Function.Injective position
  charge : Fin nuclei → ℕ
  charge_pos : ∀ a, 0 < charge a
  electrons : ℕ
  electrons_pos : 0 < electrons

/-- Unit-charge inputs carry no independently chosen charge parameters. -/
structure UnitNuclearData where
  nuclei : ℕ
  nuclei_pos : 0 < nuclei
  position : Fin nuclei → Fin 3 → ℚ
  distinct : Function.Injective position
  electrons : ℕ
  electrons_pos : 0 < electrons

def UnitNuclearData.toNuclearData (d : UnitNuclearData) : NuclearData where
  nuclei := d.nuclei
  nuclei_pos := d.nuclei_pos
  position := d.position
  distinct := d.distinct
  charge := fun _ => 1
  charge_pos := fun _ => Nat.zero_lt_one
  electrons := d.electrons
  electrons_pos := d.electrons_pos

section

theorem realPosition_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

attribute [local instance] realPosition_atLeastTwo

def realPosition (r : Fin 3 → ℚ) : Position :=
  WithLp.toLp 2 (fun a => (r a : ℝ))

end

theorem realPosition_injective : Function.Injective realPosition := by
  intro r s hrs
  funext a
  have h := congrArg (fun p : Position => p a) hrs
  change (r a : ℝ) = (s a : ℝ) at h
  exact_mod_cast h

/-- Integer positive charges satisfy the real-charge library interface. -/
def NuclearData.toNuclei (d : NuclearData) : Coulomb.Nuclei d.nuclei where
  nonempty := d.nuclei_pos
  position := fun a => realPosition (d.position a)
  distinct := realPosition_injective.comp d.distinct
  charge := fun a => (d.charge a : ℝ)
  charge_ge_one := by
    intro a
    exact_mod_cast d.charge_pos a

/-- Every normalized state ranges over the full weak H¹ fermionic space. -/
abbrev FormState (n : ℕ) := {state : Coulomb.H1Vector n // Coulomb.Antisymmetric state}

abbrev normSq {n : ℕ} (state : FormState n) := Coulomb.mass state.val
abbrev kineticEnergy {n : ℕ} (state : FormState n) := Coulomb.kinetic state.val

/-- Electronic form with kinetic coefficient `1/2`; nuclear repulsion omitted. -/
def coulombForm (d : NuclearData) (state : FormState d.electrons) : ℝ :=
  Coulomb.form d.toNuclei state.val

def unitCoulombForm (d : UnitNuclearData) (state : FormState d.electrons) : ℝ :=
  coulombForm d.toNuclearData state

/-- Variational bottom over every normalized spinful fermionic H¹ state. -/
def groundEnergy (d : NuclearData) : EReal :=
  sInf {e | ∃ state : FormState d.electrons,
    normSq state = 1 ∧ e = (coulombForm d state : EReal)}

def unitGroundEnergy (d : UnitNuclearData) : EReal :=
  sInf {e | ∃ state : FormState d.electrons,
    normSq state = 1 ∧ e = (unitCoulombForm d state : EReal)}

/-- The unit-to-binary inclusion preserves the entire variational energy. -/
theorem unit_groundEnergy_eq (d : UnitNuclearData) :
    groundEnergy d.toNuclearData = unitGroundEnergy d := rfl

/-- Nuclear singularities are integrable on the full declared form domain. -/
theorem nuclear_integrable (d : NuclearData) (state : FormState d.electrons)
    (spin : SpinConfiguration d.electrons) :
    Integrable (fun x =>
      (∑ i, Coulomb.attraction d.toNuclei (Coulomb.position x i)) *
        ‖state.val.value spin x‖ ^ 2) :=
  state.val.nuclear_integrable d.toNuclei spin

/-- Pair singularities are integrable too; no extra domain hypothesis is used. -/
theorem pair_integrable {n : ℕ} (state : FormState n) (spin : SpinConfiguration n) :
    Integrable (fun x =>
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j)
          else 0) * ‖state.val.value spin x‖ ^ 2) :=
  state.val.pair_integrable spin

/-- Explicit instance-dependent lower bound on every normalized state. -/
theorem normalized_form_lower_bound (d : NuclearData) (state : FormState d.electrons)
    (hnorm : normSq state = 1) :
    -(2 * (d.electrons : ℝ) * Coulomb.totalCharge d.toNuclei ^ 2) ≤
      coulombForm d state := by
  have h := Coulomb.form_lower_bound d.toNuclei state.val
  change _ * normSq state ≤ coulombForm d state at h
  simpa only [hnorm, mul_one] using h

/-- The continuum infimum is never minus infinity. This does not assert
attainment, binding, or a molecular excitation gap. -/
theorem groundEnergy_lower_bound (d : NuclearData) :
    (-(2 * (d.electrons : ℝ) * Coulomb.totalCharge d.toNuclei ^ 2) : ℝ) ≤
      groundEnergy d := by
  apply le_sInf
  rintro e ⟨state, hnorm, rfl⟩
  exact EReal.coe_le_coe (normalized_form_lower_bound d state hnorm)

/-- Restricting admissible states supplies an upper bound on the full bottom. -/
theorem groundEnergy_le_trial (d : NuclearData) (state : FormState d.electrons)
    (hnorm : normSq state = 1) :
    groundEnergy d ≤ (coulombForm d state : EReal) :=
  sInf_le ⟨state, hnorm, rfl⟩

/-- The lower form bound excludes minus infinity without any binding promise. -/
theorem groundEnergy_ne_bot (d : NuclearData) : groundEnergy d ≠ ⊥ := by
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le (groundEnergy_lower_bound d))

/-- Any normalized trial state excludes plus infinity; attainment is unnecessary. -/
theorem groundEnergy_ne_top (d : NuclearData) (state : FormState d.electrons)
    (hnorm : normSq state = 1) : groundEnergy d ≠ ⊤ := by
  exact ne_of_lt ((groundEnergy_le_trial d state hnorm).trans_lt (EReal.coe_lt_top _))

/-- Once a normalized trial state is provided, ordinary real threshold
accounting applies to the same continuum infimum. -/
theorem groundEnergy_coe_toReal (d : NuclearData) (state : FormState d.electrons)
    (hnorm : normSq state = 1) :
    ((groundEnergy d).toReal : EReal) = groundEnergy d :=
  EReal.coe_toReal (groundEnergy_ne_top d state hnorm) (groundEnergy_ne_bot d)

end ContinuumCoulomb

end

end OAI

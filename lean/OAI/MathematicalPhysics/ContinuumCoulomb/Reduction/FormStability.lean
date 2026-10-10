import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearRounding

namespace OAI

/-!
# Stability of the full variational bottom under nuclear rounding

The Hardy estimate is combined with coercivity of the actual Coulomb form.
Consequently rational rounding is controlled on the unrestricted fermionic
ground-energy infimum, without assuming a minimizing eigenvector or an
independent kinetic-energy bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Keeping half of the kinetic form gives a uniform coercive lower bound. -/
theorem coulomb_form_coercive {m n : ℕ} (S : Coulomb.Nuclei m)
    (state : Coulomb.H1Vector n) :
    Coulomb.kinetic state / 2 -
        4 * (n : ℝ) * Coulomb.totalCharge S ^ 2 * Coulomb.mass state ≤
      Coulomb.form S state := by
  let eta : ℝ := 1 / (16 * Coulomb.totalCharge S)
  have hZ := Coulomb.totalCharge_pos S
  have heta : 0 < eta := by dsimp [eta]; positivity
  have h := Coulomb.nuclearEnergy_bound S state heta
  have hfactor : 8 * eta * Coulomb.totalCharge S = 1 / 2 := by
    dsimp [eta]
    field_simp
    norm_num
  have hconstant : (n : ℝ) * Coulomb.totalCharge S / (4 * eta) =
      4 * (n : ℝ) * Coulomb.totalCharge S ^ 2 := by
    dsimp [eta]
    field_simp
    ring
  rw [hfactor, hconstant] at h
  have hpair := Coulomb.pairEnergy_nonneg state
  unfold Coulomb.form
  linarith

/-- The rounding estimate includes arbitrary positive nuclear charges, with
their total mass rather than their maximum charge in the error budget. -/
theorem coulomb_form_position_error {m n : ℕ} (S T : Coulomb.Nuclei m)
    (state : Coulomb.H1Vector n) {delta : ℝ}
    (hcharge : S.charge = T.charge)
    (hmove : ∀ a, ‖S.position a - T.position a‖ ≤ delta) :
    |Coulomb.form S state - Coulomb.form T state| ≤
      16 * delta * Coulomb.totalCharge S * Coulomb.kinetic state := by
  let I := fun (R : Coulomb.Nuclei m) (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) =>
    ∫ x, Coulomb.coulombKernel (Coulomb.position x i - R.position a) *
      ‖state.value s x‖ ^ 2
  let G := fun (s : Coulomb.Spins n) (i : Fin n) =>
    ∑ k : Fin 3, ∫ x, ‖state.gradient s (i, k) x‖ ^ 2
  have hG : ∀ s i, 0 ≤ G s i := by
    intro s i
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hI (R : Coulomb.Nuclei m) (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - R.position a) *
        ‖state.value s x‖ ^ 2) :=
    (state.nuclear_coulomb_integrable_bound s i (R.position a)
      (by norm_num : (0 : ℝ) < 1)).1
  have hdiff (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      I S s i a - I T s i a = ∫ x,
        (Coulomb.coulombKernel (Coulomb.position x i - S.position a) -
          Coulomb.coulombKernel (Coulomb.position x i - T.position a)) *
            ‖state.value s x‖ ^ 2 := by
    simp only [sub_mul, integral_sub (hI S s i a) (hI T s i a), I]
  have hterm (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      |S.charge a * (I S s i a - I T s i a)| ≤
        S.charge a * (8 * delta * G s i) := by
    have hz : 0 ≤ S.charge a := (by norm_num : (0 : ℝ) ≤ 1).trans (S.charge_ge_one a)
    rw [abs_mul, abs_of_nonneg hz, hdiff]
    apply mul_le_mul_of_nonneg_left _ hz
    exact (nuclear_position_rounding_bound state s i (S.position a) (T.position a)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmove a) (by norm_num)) (hG s i))
  have hnuclear : Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state =
      ∑ s, ∑ i, ∑ a, S.charge a * (I S s i a - I T s i a) := by
    rw [Coulomb.nuclearEnergy_eq_sum, Coulomb.nuclearEnergy_eq_sum, ← hcharge]
    simp only [← Finset.sum_sub_distrib, ← mul_sub, I]
  have hsum : |Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state| ≤
      ∑ s, ∑ i, ∑ a, S.charge a * (8 * delta * G s i) := by
    rw [hnuclear]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro s _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun a _ => hterm s i a)
  have htotal : (∑ s, ∑ i, ∑ a, S.charge a * (8 * delta * G s i)) =
      16 * delta * Coulomb.totalCharge S * Coulomb.kinetic state := by
    simp only [← Finset.sum_mul]
    unfold G Coulomb.kinetic Coulomb.totalCharge
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    ring
  have heq : Coulomb.form S state - Coulomb.form T state =
      -(Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state) := by
    unfold Coulomb.form
    ring
  rw [heq, abs_neg]
  exact hsum.trans_eq htotal

/-- The same full fermionic bottom for real positions, prior to rationalization. -/
def formGroundEnergy {m : ℕ} (S : Coulomb.Nuclei m) (n : ℕ) : EReal :=
  sInf {e | ∃ state : FormState n,
    normSq state = 1 ∧ e = (Coulomb.form S state.val : EReal)}

theorem groundEnergy_eq_formGroundEnergy (d : NuclearData) :
    groundEnergy d = formGroundEnergy d.toNuclei d.electrons := rfl

theorem formGroundEnergy_le_trial {m n : ℕ} (S : Coulomb.Nuclei m)
    (state : FormState n) (hnorm : normSq state = 1) :
    formGroundEnergy S n ≤ (Coulomb.form S state.val : EReal) :=
  sInf_le ⟨state, hnorm, rfl⟩

theorem formGroundEnergy_lower_of_forall {m n : ℕ} (S : Coulomb.Nuclei m) (a : ℝ)
    (ha : ∀ state : FormState n, normSq state = 1 → a ≤ Coulomb.form S state.val) :
    (a : EReal) ≤ formGroundEnergy S n := by
  apply le_sInf
  rintro e ⟨state, hnorm, rfl⟩
  exact EReal.coe_le_coe (ha state hnorm)

theorem formGroundEnergy_finite {m n : ℕ} (S : Coulomb.Nuclei m)
    (trial : FormState n) (htrial : normSq trial = 1) :
    formGroundEnergy S n ≠ ⊤ ∧ formGroundEnergy S n ≠ ⊥ := by
  constructor
  · exact ne_of_lt ((formGroundEnergy_le_trial S trial htrial).trans_lt (EReal.coe_lt_top _))
  · apply ne_of_gt
    apply (EReal.bot_lt_coe (-(2 * (n : ℝ) * Coulomb.totalCharge S ^ 2))).trans_le
    apply formGroundEnergy_lower_of_forall
    intro state hnorm
    have h := Coulomb.form_lower_bound S state.val
    change _ * normSq state ≤ _ at h
    simpa only [hnorm, mul_one] using h

/-- A quantitative change of the full bottom under nuclear movement. The
single normalized trial proves both bottoms finite; it need not minimize.
The factor in parentheses is automatically nonnegative by coercivity. -/
theorem formGroundEnergy_position_stability {m n : ℕ} (S T : Coulomb.Nuclei m)
    (trial : FormState n) (htrial : normSq trial = 1) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hcharge : S.charge = T.charge)
    (hmove : ∀ a, ‖S.position a - T.position a‖ ≤ delta)
    (hsmall : 32 * delta * Coulomb.totalCharge S ≤ 1) :
    |(formGroundEnergy T n).toReal - (formGroundEnergy S n).toReal| ≤
      32 * delta * Coulomb.totalCharge S *
        ((formGroundEnergy S n).toReal + 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2) := by
  let theta : ℝ := 16 * delta * Coulomb.totalCharge S
  let C : ℝ := 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2
  let E : ℝ := (formGroundEnergy S n).toReal
  let F : ℝ := (formGroundEnergy T n).toReal
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact mul_nonneg (mul_nonneg (by norm_num) hdelta) (Coulomb.totalCharge_pos S).le
  have hslower : 0 ≤ 1 - 2 * theta := by dsimp [theta]; nlinarith
  have hsupper : 0 < 1 + 2 * theta := by linarith
  have hEcoe : (E : EReal) = formGroundEnergy S n :=
    EReal.coe_toReal (formGroundEnergy_finite S trial htrial).1
      (formGroundEnergy_finite S trial htrial).2
  have hFcoe : (F : EReal) = formGroundEnergy T n :=
    EReal.coe_toReal (formGroundEnergy_finite T trial htrial).1
      (formGroundEnergy_finite T trial htrial).2
  have hEtrial (u : FormState n) (hu : normSq u = 1) : E ≤ Coulomb.form S u.val := by
    apply EReal.coe_le_coe_iff.mp
    rw [hEcoe]
    exact formGroundEnergy_le_trial S u hu
  have hFtrial (u : FormState n) (hu : normSq u = 1) : F ≤ Coulomb.form T u.val := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    exact formGroundEnergy_le_trial T u hu
  have hpoint (u : FormState n) (hu : normSq u = 1) :
      (1 - 2 * theta) * Coulomb.form S u.val - 2 * theta * C ≤ Coulomb.form T u.val ∧
      Coulomb.form T u.val ≤ (1 + 2 * theta) * Coulomb.form S u.val + 2 * theta * C := by
    have hcoercive := coulomb_form_coercive S u.val
    change Coulomb.kinetic u.val / 2 - C * normSq u ≤ Coulomb.form S u.val at hcoercive
    rw [hu, mul_one] at hcoercive
    have hk := mul_le_mul_of_nonneg_left hcoercive (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htheta)
    have he := coulomb_form_position_error S T u.val hcharge hmove
    change |Coulomb.form S u.val - Coulomb.form T u.val| ≤ theta * Coulomb.kinetic u.val at he
    obtain ⟨hl, hr⟩ := abs_le.mp he
    constructor <;> nlinarith
  have hlower : (1 - 2 * theta) * E - 2 * theta * C ≤ F := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    apply formGroundEnergy_lower_of_forall
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hEtrial u hu) hslower
    have hp := (hpoint u hu).1
    linarith
  have hupper : F ≤ (1 + 2 * theta) * E + 2 * theta * C := by
    have haux : (F - 2 * theta * C) / (1 + 2 * theta) ≤ E := by
      apply EReal.coe_le_coe_iff.mp
      rw [hEcoe]
      apply formGroundEnergy_lower_of_forall
      intro u hu
      apply (div_le_iff₀ hsupper).2
      have h := hFtrial u hu
      have hp := (hpoint u hu).2
      nlinarith
    have h := (div_le_iff₀ hsupper).mp haux
    nlinarith
  change |F - E| ≤ _
  have hbound : |F - E| ≤ 2 * theta * (E + C) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  convert hbound using 1
  dsimp [theta, E, C]
  ring

/-- An explicit trial energy supplies a computable rounding budget, without
requiring the exact real ground energy as input. -/
theorem formGroundEnergy_position_stability_trial {m n : ℕ} (S T : Coulomb.Nuclei m)
    (trial : FormState n) (htrial : normSq trial = 1) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hcharge : S.charge = T.charge)
    (hmove : ∀ a, ‖S.position a - T.position a‖ ≤ delta)
    (hsmall : 32 * delta * Coulomb.totalCharge S ≤ 1) :
    |(formGroundEnergy T n).toReal - (formGroundEnergy S n).toReal| ≤
      32 * delta * Coulomb.totalCharge S *
        (Coulomb.form S trial.val + 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2) := by
  apply (formGroundEnergy_position_stability S T trial htrial hdelta hcharge hmove hsmall).trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add _ le_rfl
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal (formGroundEnergy_finite S trial htrial).1
      (formGroundEnergy_finite S trial htrial).2]
    exact formGroundEnergy_le_trial S trial htrial
  · exact mul_nonneg (mul_nonneg (by norm_num) hdelta) (Coulomb.totalCharge_pos S).le

end ContinuumCoulomb

end

end OAI

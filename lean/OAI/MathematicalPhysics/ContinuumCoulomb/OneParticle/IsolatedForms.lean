import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.BinaryWellCharges

namespace OAI

/-!
# Isolated-well energy forms on the actual weak H¹ domain

The perturbation bounds here concern the full one-electron form, including
both Coulomb poles and the capped background. They give the shifted relative
form comparison used before constructing isolated eigenfunctions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def singlePoleEnergy (a : Position) (state : Coulomb.H1Vector 1) : ℝ :=
  ∑ spin, ∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - a) *
    ‖state.value spin x‖ ^ 2

def hydrogenForm (a : Position) (state : Coulomb.H1Vector 1) : ℝ :=
  Coulomb.kinetic state - singlePoleEnergy a state

def backgroundEnergy {m : ℕ} (D q q' : ℝ) (center displacement : Fin m → Position)
    (site : Fin m) (state : Coulomb.H1Vector 1) : ℝ :=
  ∑ spin, ∫ x, backgroundPotential D q q' center displacement site
    (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2

def isolatedWellForm {m : ℕ} (D q q' : ℝ) (center displacement : Fin m → Position)
    (site : Fin m) (state : Coulomb.H1Vector 1) : ℝ :=
  Coulomb.kinetic state - q * singlePoleEnergy (center site) state -
    q' * singlePoleEnergy (center site + displacement site) state -
      backgroundEnergy D q q' center displacement site state

theorem singlePoleEnergy_nonneg (a : Position) (state : Coulomb.H1Vector 1) :
    0 ≤ singlePoleEnergy a state := by
  apply Finset.sum_nonneg
  intro spin _
  exact integral_nonneg fun x => by unfold Coulomb.coulombKernel; positivity

theorem singlePoleEnergy_bound (a : Position) (state : Coulomb.H1Vector 1)
    {eta : ℝ} (heta : 0 < eta) :
    singlePoleEnergy a state ≤ 8 * eta * Coulomb.kinetic state +
      (1 / (4 * eta)) * Coulomb.mass state := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun spin _ =>
    (state.nuclear_coulomb_integrable_bound spin 0 a heta).2
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Coulomb.kinetic, Coulomb.mass,
    Fintype.sum_prod_type, Fin.sum_univ_one]
  ring

theorem hydrogenForm_coercive (a : Position) (state : Coulomb.H1Vector 1) :
    Coulomb.kinetic state / 2 - 4 * Coulomb.mass state ≤ hydrogenForm a state := by
  have h := singlePoleEnergy_bound a state (by norm_num : (0 : ℝ) < 1 / 16)
  norm_num at h
  unfold hydrogenForm
  linarith

theorem background_energy_integrable {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) (spin : Coulomb.Spins 1) :
    Integrable (fun x => backgroundPotential D q q' center displacement site
      (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2) := by
  have hrho := (state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hcont : Continuous (fun x : Configuration 1 =>
      backgroundPotential D q q' center displacement site (Coulomb.position x 0)) := by
    apply (backgroundPotential_contDiff_two hD center displacement hdisp site).continuous.comp
    unfold Coulomb.position
    fun_prop
  apply (hrho.const_mul (48 * m / D)).mono'
    (hcont.aestronglyMeasurable.mul ((state.value_L2 spin).aestronglyMeasurable.norm.pow 2))
  exact Filter.Eventually.of_forall fun x => by
    have h := backgroundPotential_bounds hD hq hq1 hq' hq'1 center displacement hdisp site
      (Coulomb.position x 0)
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h.1, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right h.2 (sq_nonneg _)

theorem backgroundEnergy_bounds {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    0 ≤ backgroundEnergy D q q' center displacement site state ∧
      backgroundEnergy D q q' center displacement site state ≤
        (48 * m / D) * Coulomb.mass state := by
  constructor
  · exact Finset.sum_nonneg fun spin _ => integral_nonneg fun x =>
      mul_nonneg (backgroundPotential_bounds hD hq hq1 hq' hq'1 center displacement
        hdisp site (Coulomb.position x 0)).1 (sq_nonneg _)
  · unfold backgroundEnergy Coulomb.mass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro spin _
    rw [← integral_const_mul]
    apply integral_mono
      (background_energy_integrable hD hq hq1 hq' hq'1 center displacement hdisp site state spin)
      (((state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _)
    intro x
    exact mul_le_mul_of_nonneg_right
      (backgroundPotential_bounds hD hq hq1 hq' hq'1 center displacement hdisp site
        (Coulomb.position x 0)).2 (sq_nonneg _)

theorem isolatedWellForm_coercive {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    Coulomb.kinetic state / 2 - (16 + 48 * m / D) * Coulomb.mass state ≤
      isolatedWellForm D q q' center displacement site state := by
  have hp := singlePoleEnergy_bound (center site) state (by norm_num : (0 : ℝ) < 1 / 32)
  have hs := singlePoleEnergy_bound (center site + displacement site) state
    (by norm_num : (0 : ℝ) < 1 / 32)
  have hqp := mul_le_of_le_one_left (singlePoleEnergy_nonneg (center site) state) hq1
  have hqs := mul_le_of_le_one_left
    (singlePoleEnergy_nonneg (center site + displacement site) state) hq'1
  have hb := (backgroundEnergy_bounds hD hq hq1 hq' hq'1
    center displacement hdisp site state).2
  norm_num at hp hs
  unfold isolatedWellForm
  linarith

theorem isolatedWellForm_difference {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    isolatedWellForm D q q' center displacement site state - hydrogenForm (center site) state =
      ∑ spin, ∫ x, isolatedPerturbation D q q' center displacement site
        (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2 := by
  have heq (spin : Coulomb.Spins 1) :
      (∫ x, isolatedPerturbation D q q' center displacement site
        (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2) =
      (1 - q) * (∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - center site) *
        ‖state.value spin x‖ ^ 2) -
      q' * (∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - (center site + displacement site)) *
        ‖state.value spin x‖ ^ 2) -
      (∫ x, backgroundPotential D q q' center displacement site
        (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2) := by
    have hp := (state.nuclear_coulomb_integrable_bound spin 0 (center site)
      (by norm_num : (0 : ℝ) < 1)).1
    have hs := (state.nuclear_coulomb_integrable_bound spin 0 (center site + displacement site)
      (by norm_num : (0 : ℝ) < 1)).1
    have hb := background_energy_integrable hD hq hq1 hq' hq'1
      center displacement hdisp site state spin
    have hsub : ∀ x : Configuration 1,
        Coulomb.position x 0 - center site - displacement site =
          Coulomb.position x 0 - (center site + displacement site) := by intro x; abel
    let p := fun x : Configuration 1 =>
      Coulomb.coulombKernel (Coulomb.position x 0 - center site) * ‖state.value spin x‖ ^ 2
    let s := fun x : Configuration 1 =>
      Coulomb.coulombKernel (Coulomb.position x 0 - (center site + displacement site)) *
        ‖state.value spin x‖ ^ 2
    let b := fun x : Configuration 1 =>
      backgroundPotential D q q' center displacement site (Coulomb.position x 0) *
        ‖state.value spin x‖ ^ 2
    have hpoint : (fun x => isolatedPerturbation D q q' center displacement site
        (Coulomb.position x 0) * ‖state.value spin x‖ ^ 2) =
        (fun x => (1 - q) * p x - q' * s x - b x) := by
      funext x
      dsimp [isolatedPerturbation, p, s, b]
      rw [hsub]
      ring
    rw [hpoint]
    have hsum := integral_sub ((hp.const_mul (1 - q)).sub (hs.const_mul q')) hb
    change (∫ x, (1 - q) * p x - q' * s x - b x) = _ at hsum
    have hsum' := integral_sub (hp.const_mul (1 - q)) (hs.const_mul q')
    change (∫ x, (1 - q) * p x - q' * s x) = _ at hsum'
    rw [hsum]
    dsimp only [Pi.sub_apply]
    rw [hsum']
    simp only [integral_const_mul]
  simp_rw [heq]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    isolatedWellForm, hydrogenForm, singlePoleEnergy, backgroundEnergy]
  ring

theorem isolatedWellForm_small_difference {m : ℕ} {D q q' epsilon : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hprimary : |1 - q| ≤ epsilon) (hsecondary : q' ≤ epsilon)
    (hbackground : 48 * m / D ≤ epsilon)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    |isolatedWellForm D q q' center displacement site state - hydrogenForm (center site) state| ≤
      5 * epsilon * (Coulomb.kinetic state + Coulomb.mass state) := by
  have hepsilon : 0 ≤ epsilon := hq'.trans hsecondary
  have hp0 := singlePoleEnergy_nonneg (center site) state
  have hs0 := singlePoleEnergy_nonneg (center site + displacement site) state
  have hp := singlePoleEnergy_bound (center site) state (by norm_num : (0 : ℝ) < 1 / 8)
  have hs := singlePoleEnergy_bound (center site + displacement site) state
    (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num at hp hs
  have hb := backgroundEnergy_bounds hD hq hq1 hq' hq'1 center displacement hdisp site state
  have hdefect : |1 - q| * singlePoleEnergy (center site) state ≤
      epsilon * (Coulomb.kinetic state + 2 * Coulomb.mass state) :=
    mul_le_mul hprimary hp hp0 hepsilon
  have hsecond : q' * singlePoleEnergy (center site + displacement site) state ≤
      epsilon * (Coulomb.kinetic state + 2 * Coulomb.mass state) :=
    mul_le_mul hsecondary hs hs0 hepsilon
  have hbg := hb.2.trans (mul_le_mul_of_nonneg_right hbackground (Coulomb.mass_nonneg state))
  have heq : isolatedWellForm D q q' center displacement site state -
      hydrogenForm (center site) state =
      (1 - q) * singlePoleEnergy (center site) state -
        q' * singlePoleEnergy (center site + displacement site) state -
        backgroundEnergy D q q' center displacement site state := by
    unfold isolatedWellForm hydrogenForm
    ring
  rw [heq]
  calc
    _ ≤ |(1 - q) * singlePoleEnergy (center site) state| +
        |q' * singlePoleEnergy (center site + displacement site) state| +
        |backgroundEnergy D q q' center displacement site state| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |1 - q| * singlePoleEnergy (center site) state +
        q' * singlePoleEnergy (center site + displacement site) state +
        backgroundEnergy D q q' center displacement site state := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq',
        abs_of_nonneg hs0, abs_of_nonneg hb.1]
    _ ≤ _ := by nlinarith [mul_nonneg hepsilon (Coulomb.kinetic_nonneg state)]

/-- The actual isolated well is a small relative perturbation of the shifted
hydrogen form. This holds on every spinful weak-H¹ state. -/
theorem isolatedWellForm_relative {m : ℕ} {D q q' epsilon : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hprimary : |1 - q| ≤ epsilon) (hsecondary : q' ≤ epsilon)
    (hbackground : 48 * m / D ≤ epsilon)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    |isolatedWellForm D q q' center displacement site state - hydrogenForm (center site) state| ≤
      10 * epsilon * (hydrogenForm (center site) state + 5 * Coulomb.mass state) := by
  have h := isolatedWellForm_small_difference hD hq hq1 hq' hq'1 hprimary hsecondary
    hbackground center displacement hdisp site state
  have hc := hydrogenForm_coercive (center site) state
  have hepsilon : 0 ≤ epsilon := hq'.trans hsecondary
  exact h.trans (by nlinarith [mul_nonneg hepsilon (Coulomb.mass_nonneg state),
    mul_le_mul_of_nonneg_left hc hepsilon])

end ContinuumCoulomb

end

end OAI

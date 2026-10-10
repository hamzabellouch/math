import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.IsolatedForms

namespace OAI

/-!
# Motion of secondary nuclei in capped backgrounds

The cap depends only on the fixed primary centre. On its nonzero support
every permitted secondary pole is at least `D/32` away. Thus its motion has
a uniform `D⁻²` potential bound, before any isolated eigenstate is chosen.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem cappedSitePotential_displacement_bound {D q q' : ℝ} (hD : 128 ≤ D)
    (hq' : 0 ≤ q') (center a b x : Position) (ha : ‖a‖ ≤ 4) (hb : ‖b‖ ≤ 4) :
    |cappedSitePotential D q q' center a x - cappedSitePotential D q q' center b x| ≤
      2048 * q' / D ^ 2 * ‖a - b‖ := by
  have hD0 : 0 < D := by linarith
  by_cases hc : wellCap (‖x - center‖ / D) = 0
  · simp only [cappedSitePotential, hc, zero_mul, sub_self, abs_zero]
    positivity
  have hr := wellCap_nonzero_radius hD0 hc
  have hdist (c : Position) (hc4 : ‖c‖ ≤ 4) : D / 32 ≤ ‖x - center - c‖ := by
    have ht : ‖x - center‖ ≤ ‖x - center - c‖ + ‖c‖ := by
      calc
        _ = ‖(x - center - c) + c‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  have hkernel (c : Position) (hc4 : ‖c‖ ≤ 4) :
      Coulomb.coulombKernel (x - center - c) ≤ 32 / D := by
    unfold Coulomb.coulombKernel
    calc
      _ ≤ (D / 32)⁻¹ := inv_anti₀ (by positivity) (hdist c hc4)
      _ = _ := by ring
  have hsq (c : Position) (hc4 : ‖c‖ ≤ 4) :
      Coulomb.coulombKernel (x - center - c) ^ 2 ≤ (32 / D) ^ 2 :=
    (sq_le_sq₀ (by unfold Coulomb.coulombKernel; positivity) (by positivity)).mpr (hkernel c hc4)
  have heq : cappedSitePotential D q q' center a x - cappedSitePotential D q q' center b x =
      wellCap (‖x - center‖ / D) * q' *
        (Coulomb.coulombKernel (x - center - a) - Coulomb.coulombKernel (x - center - b)) := by
    unfold cappedSitePotential sitePotential
    ring
  have hshift := coulomb_kernel_shift_bound (x - center) a b
  have hsum : Coulomb.coulombKernel (x - center - a) ^ 2 +
      Coulomb.coulombKernel (x - center - b) ^ 2 ≤ 2048 / D ^ 2 := by
    have h := add_le_add (hsq a ha) (hsq b hb)
    convert h using 1
    ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg (wellCap_bounds _).1, abs_of_nonneg hq']
  calc
    _ ≤ q' * |Coulomb.coulombKernel (x - center - a) -
        Coulomb.coulombKernel (x - center - b)| :=
      mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hq' (wellCap_bounds _).2) (abs_nonneg _)
    _ ≤ q' * (‖a - b‖ * (2048 / D ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (hshift.trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))) hq'
    _ = _ := by ring

theorem backgroundPotential_displacement_bound {m : ℕ} {D q q' delta : ℝ}
    (hD : 128 ≤ D) (hq' : 0 ≤ q') (hdelta : 0 ≤ delta)
    (center a b : Fin m → Position) (ha : ∀ j, ‖a j‖ ≤ 4) (hb : ∀ j, ‖b j‖ ≤ 4)
    (hmove : ∀ j, ‖a j - b j‖ ≤ delta) (site : Fin m) (x : Position) :
    |backgroundPotential D q q' center a site x -
      backgroundPotential D q q' center b site x| ≤
      2048 * q' * m / D ^ 2 * delta := by
  unfold backgroundPotential
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(if j = site then 0 else cappedSitePotential D q q' (center j) (a j) x) -
        (if j = site then 0 else cappedSitePotential D q q' (center j) (b j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, 2048 * q' / D ^ 2 * delta := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · simp only [sub_self, abs_zero]
        positivity
      · exact (cappedSitePotential_displacement_bound hD hq' (center j) (a j) (b j) x
          (ha j) (hb j)).trans
            (mul_le_mul_of_nonneg_left (hmove j) (by positivity))
    _ = _ := by simp; ring

theorem singlePoleEnergy_position_bound (a b : Position) (state : Coulomb.H1Vector 1) :
    |singlePoleEnergy a state - singlePoleEnergy b state| ≤
      16 * ‖a - b‖ * Coulomb.kinetic state := by
  unfold singlePoleEnergy
  rw [← Finset.sum_sub_distrib]
  have hterm (spin : Coulomb.Spins 1) :
      |(∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - a) * ‖state.value spin x‖ ^ 2) -
        (∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - b) * ‖state.value spin x‖ ^ 2)| ≤
        8 * ‖a - b‖ * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (0, k) x‖ ^ 2 := by
    rw [← integral_sub
      (state.nuclear_coulomb_integrable_bound spin 0 a (by norm_num : (0 : ℝ) < 1)).1
      (state.nuclear_coulomb_integrable_bound spin 0 b (by norm_num : (0 : ℝ) < 1)).1]
    simpa only [← sub_mul] using nuclear_position_rounding_bound state spin 0 a b
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun spin _ => hterm spin).trans_eq
  simp only [← Finset.mul_sum, Coulomb.kinetic, Fintype.sum_prod_type, Fin.sum_univ_one]
  ring

theorem backgroundEnergy_displacement_bound {m : ℕ} {D q q' delta : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hdelta : 0 ≤ delta) (center a b : Fin m → Position)
    (ha : ∀ j, ‖a j‖ ≤ 4) (hb : ∀ j, ‖b j‖ ≤ 4)
    (hmove : ∀ j, ‖a j - b j‖ ≤ delta) (site : Fin m) (state : Coulomb.H1Vector 1) :
    |backgroundEnergy D q q' center a site state -
      backgroundEnergy D q q' center b site state| ≤
      (2048 * q' * m / D ^ 2 * delta) * Coulomb.mass state := by
  let C := 2048 * q' * m / D ^ 2 * delta
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm (spin : Coulomb.Spins 1) :
      |(∫ x, backgroundPotential D q q' center a site (Coulomb.position x 0) *
          ‖state.value spin x‖ ^ 2) -
        (∫ x, backgroundPotential D q q' center b site (Coulomb.position x 0) *
          ‖state.value spin x‖ ^ 2)| ≤ C * ∫ x, ‖state.value spin x‖ ^ 2 := by
    have hia := background_energy_integrable hD hq hq1 hq' hq'1 center a ha site state spin
    have hib := background_energy_integrable hD hq hq1 hq' hq'1 center b hb site state spin
    rw [← integral_sub hia hib, ← integral_const_mul]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono (hia.sub hib).abs
      (((state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul C)
    intro x
    dsimp only [Pi.sub_apply]
    rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖state.value spin x‖)]
    exact mul_le_mul_of_nonneg_right
      (backgroundPotential_displacement_bound hD hq' hdelta center a b ha hb hmove site
        (Coulomb.position x 0)) (sq_nonneg _)
  unfold backgroundEnergy
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun spin _ => hterm spin).trans_eq (by rw [← Finset.mul_sum]; rfl))

/-- Motion of the own pole costs a kinetic term; motion of all the other
poles costs only the small bounded-background term. -/
theorem isolatedWellForm_displacement_bound {m : ℕ} {D q q' delta : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hdelta : 0 ≤ delta) (center a b : Fin m → Position)
    (ha : ∀ j, ‖a j‖ ≤ 4) (hb : ∀ j, ‖b j‖ ≤ 4)
    (hmove : ∀ j, ‖a j - b j‖ ≤ delta) (site : Fin m) (state : Coulomb.H1Vector 1) :
    |isolatedWellForm D q q' center a site state -
      isolatedWellForm D q q' center b site state| ≤
      16 * q' * ‖a site - b site‖ * Coulomb.kinetic state +
        (2048 * q' * m / D ^ 2 * delta) * Coulomb.mass state := by
  have hp := singlePoleEnergy_position_bound (center site + a site) (center site + b site) state
  have hcancel : (center site + a site) - (center site + b site) = a site - b site := by abel
  rw [hcancel] at hp
  have hbg := backgroundEnergy_displacement_bound hD hq hq1 hq' hq'1 hdelta
    center a b ha hb hmove site state
  have heq : isolatedWellForm D q q' center a site state -
      isolatedWellForm D q q' center b site state =
      -(q' * (singlePoleEnergy (center site + a site) state -
        singlePoleEnergy (center site + b site) state)) -
        (backgroundEnergy D q q' center a site state -
          backgroundEnergy D q q' center b site state) := by
    unfold isolatedWellForm
    ring
  rw [heq]
  apply (abs_sub _ _).trans
  rw [abs_neg, abs_mul, abs_of_nonneg hq']
  have h := add_le_add (mul_le_mul_of_nonneg_left hp hq') hbg
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI

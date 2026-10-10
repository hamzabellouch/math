import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WellCapRegularity
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearRounding

namespace OAI

/-!
# Actual isolated-well perturbation on weak H¹ states

The difference from a unit hydrogen centre is the small change of primary
charge, the weak secondary Coulomb pole, and the bounded capped background.
No isolated eigenfunction or perturbative spectral conclusion is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem nuclear_mul_memLp {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a : Position) :
    MemLp (fun x => (Coulomb.coulombKernel (Coulomb.position x i - a) : ℂ) *
      state.value spin x) 2 := by
  have hm := Coulomb.measurable_hardyCoulomb i (Coulomb.nuclearHardyCoordinates i a)
  change Measurable (fun x =>
    Coulomb.hardyCoulomb i (Coulomb.nuclearHardyCoordinates i a) x) at hm
  simp only [Coulomb.hardyCoulomb_nuclear] at hm
  have hmeas : AEStronglyMeasurable (fun x =>
      (Coulomb.coulombKernel (Coulomb.position x i - a) : ℂ) * state.value spin x) volume :=
    hm.complex_ofReal.aestronglyMeasurable.mul (state.value_L2 spin).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    (nuclear_hardy_square state spin i a).1

def isolatedPerturbation {m : ℕ} (D q q' : ℝ) (center displacement : Fin m → Position)
    (site : Fin m) (x : Position) : ℝ :=
  (1 - q) * Coulomb.coulombKernel (x - center site) -
    q' * Coulomb.coulombKernel (x - center site - displacement site) -
      backgroundPotential D q q' center displacement site x

theorem background_mul_memLp {m n : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector n) (spin : Coulomb.Spins n) (i : Fin n) :
    MemLp (fun x => (backgroundPotential D q q' center displacement site
      (Coulomb.position x i) : ℂ) * state.value spin x) 2 := by
  apply Coulomb.memLp_two_real_mul (state.value_L2 spin)
  · apply (backgroundPotential_contDiff_two hD center displacement hdisp site).continuous.comp
    unfold Coulomb.position
    fun_prop
  · intro x
    have h := backgroundPotential_bounds hD hq hq1 hq' hq'1 center displacement hdisp site
      (Coulomb.position x i)
    exact (abs_of_nonneg h.1).trans_le h.2

theorem isolatedPerturbation_mul_memLp {m n : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector n) (spin : Coulomb.Spins n) (i : Fin n) :
    MemLp (fun x => (isolatedPerturbation D q q' center displacement site
      (Coulomb.position x i) : ℂ) * state.value spin x) 2 := by
  have hp := (nuclear_mul_memLp state spin i (center site)).const_mul ((1 - q : ℝ) : ℂ)
  have hs := (nuclear_mul_memLp state spin i (center site + displacement site)).const_mul (q' : ℂ)
  have hb := background_mul_memLp hD hq hq1 hq' hq'1 center displacement hdisp site state spin i
  convert (hp.sub hs).sub hb using 1
  funext x
  dsimp [isolatedPerturbation]
  have he : Coulomb.position x i - center site - displacement site =
      Coulomb.position x i - (center site + displacement site) := by abel
  rw [he]
  push_cast
  ring

private theorem norm_sub_sub_sq_le (a b c : ℂ) :
    ‖a - b - c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have htri : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hsq := (sq_le_sq₀ (norm_nonneg (a - b - c))
    (by positivity : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖)).mpr htri
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

theorem isolatedPerturbation_spin_norm_bound {m n : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector n) (spin : Coulomb.Spins n) (i : Fin n) :
    (∫ x, ‖(isolatedPerturbation D q q' center displacement site
      (Coulomb.position x i) : ℂ) * state.value spin x‖ ^ 2) ≤
      12 * ((1 - q) ^ 2 + q' ^ 2) *
        (∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2) +
      3 * (48 * m / D) ^ 2 * (∫ x, ‖state.value spin x‖ ^ 2) := by
  have hD0 : 0 < D := by linarith
  let a := center site
  let b := center site + displacement site
  let B : ℝ := 48 * m / D
  let u := state.value spin
  let ka := fun x : Configuration n => Coulomb.coulombKernel (Coulomb.position x i - a)
  let kb := fun x : Configuration n => Coulomb.coulombKernel (Coulomb.position x i - b)
  have hIa := (nuclear_hardy_square state spin i a).1
  have hIb := (nuclear_hardy_square state spin i b).1
  have hIu := (state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  change Integrable (fun x => ka x ^ 2 * ‖u x‖ ^ 2) at hIa
  change Integrable (fun x => kb x ^ 2 * ‖u x‖ ^ 2) at hIb
  change Integrable (fun x => ‖u x‖ ^ 2) at hIu
  have hI := (isolatedPerturbation_mul_memLp hD hq hq1 hq' hq'1
    center displacement hdisp site state spin i).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let majorant := fun x : Configuration n => 3 *
    ((1 - q) ^ 2 * (ka x ^ 2 * ‖u x‖ ^ 2) +
      q' ^ 2 * (kb x ^ 2 * ‖u x‖ ^ 2) + B ^ 2 * ‖u x‖ ^ 2)
  have hmajorant : Integrable majorant :=
    (((hIa.const_mul ((1 - q) ^ 2)).add (hIb.const_mul (q' ^ 2))).add
      (hIu.const_mul (B ^ 2))).const_mul 3
  have hpoint (x : Configuration n) :
      ‖(isolatedPerturbation D q q' center displacement site
        (Coulomb.position x i) : ℂ) * u x‖ ^ 2 ≤ majorant x := by
    let w := backgroundPotential D q q' center displacement site (Coulomb.position x i)
    have hw := backgroundPotential_bounds hD hq hq1 hq' hq'1 center displacement hdisp site
      (Coulomb.position x i)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hw2 : w ^ 2 ≤ B ^ 2 := by
      change 0 ≤ w ∧ w ≤ B at hw
      nlinarith
    have he : (isolatedPerturbation D q q' center displacement site
        (Coulomb.position x i) : ℂ) * u x =
        ((1 - q : ℝ) : ℂ) * ((ka x : ℂ) * u x) -
          (q' : ℂ) * ((kb x : ℂ) * u x) - (w : ℂ) * u x := by
      dsimp [isolatedPerturbation, ka, kb, a, b, w]
      have hsub : Coulomb.position x i - center site - displacement site =
          Coulomb.position x i - (center site + displacement site) := by abel
      rw [hsub]
      push_cast
      ring
    rw [he]
    have hnorm := norm_sub_sub_sq_le
      (((1 - q : ℝ) : ℂ) * ((ka x : ℂ) * u x))
      ((q' : ℂ) * ((kb x : ℂ) * u x)) ((w : ℂ) * u x)
    simp only [Coulomb.norm_real_mul_sq] at hnorm
    apply hnorm.trans
    change 3 * (_ + _ + w ^ 2 * ‖u x‖ ^ 2) ≤ 3 * (_ + _ + B ^ 2 * ‖u x‖ ^ 2)
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hw2 (sq_nonneg _))) (by norm_num)
  have hbound := integral_mono hI hmajorant hpoint
  have hmaj : (∫ x, majorant x) = 3 *
      ((1 - q) ^ 2 * (∫ x, ka x ^ 2 * ‖u x‖ ^ 2) +
        q' ^ 2 * (∫ x, kb x ^ 2 * ‖u x‖ ^ 2) +
          B ^ 2 * (∫ x, ‖u x‖ ^ 2)) := by
    have hsum := integral_add
      ((hIa.const_mul ((1 - q) ^ 2)).add (hIb.const_mul (q' ^ 2))) (hIu.const_mul (B ^ 2))
    change (∫ x, (1 - q) ^ 2 * (ka x ^ 2 * ‖u x‖ ^ 2) +
      q' ^ 2 * (kb x ^ 2 * ‖u x‖ ^ 2) + B ^ 2 * ‖u x‖ ^ 2) = _ at hsum
    have hsum' := integral_add (hIa.const_mul ((1 - q) ^ 2)) (hIb.const_mul (q' ^ 2))
    change (∫ x, (1 - q) ^ 2 * (ka x ^ 2 * ‖u x‖ ^ 2) +
      q' ^ 2 * (kb x ^ 2 * ‖u x‖ ^ 2)) = _ at hsum'
    rw [integral_const_mul, hsum]
    dsimp only [Pi.add_apply]
    rw [hsum']
    simp only [integral_const_mul]
  rw [hmaj] at hbound
  have ha := mul_le_mul_of_nonneg_left (nuclear_hardy_square state spin i a).2
    (sq_nonneg (1 - q))
  have hb := mul_le_mul_of_nonneg_left (nuclear_hardy_square state spin i b).2 (sq_nonneg q')
  change (1 - q) ^ 2 * (∫ x, ka x ^ 2 * ‖u x‖ ^ 2) ≤ _ at ha
  change q' ^ 2 * (∫ x, kb x ^ 2 * ‖u x‖ ^ 2) ≤ _ at hb
  change _ ≤ 12 * _ * _ + 3 * B ^ 2 * (∫ x, ‖u x‖ ^ 2)
  linarith

/-- The operator estimate for an arbitrary one-electron spinful weak-H¹ state. -/
theorem isolatedPerturbation_norm_bound {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    (∑ spin, ∫ x, ‖(isolatedPerturbation D q q' center displacement site
      (Coulomb.position x 0) : ℂ) * state.value spin x‖ ^ 2) ≤
      24 * ((1 - q) ^ 2 + q' ^ 2) * Coulomb.kinetic state +
        3 * (48 * m / D) ^ 2 * Coulomb.mass state := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun spin _ =>
    isolatedPerturbation_spin_norm_bound hD hq hq1 hq' hq'1 center displacement hdisp
      site state spin 0)
  apply h.trans_eq
  unfold Coulomb.kinetic Coulomb.mass
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
  ring

theorem isolatedPerturbation_small_norm_bound {m : ℕ} {D q q' epsilon : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hprimary : |1 - q| ≤ epsilon) (hsecondary : q' ≤ epsilon)
    (hbackground : 48 * m / D ≤ epsilon)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (state : Coulomb.H1Vector 1) :
    (∑ spin, ∫ x, ‖(isolatedPerturbation D q q' center displacement site
      (Coulomb.position x 0) : ℂ) * state.value spin x‖ ^ 2) ≤
        48 * epsilon ^ 2 * (Coulomb.kinetic state + Coulomb.mass state) := by
  have hepsilon : 0 ≤ epsilon := hq'.trans hsecondary
  have hp : (1 - q) ^ 2 ≤ epsilon ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (1 - q)) hepsilon).mpr hprimary
  have hs := (sq_le_sq₀ hq' hepsilon).mpr hsecondary
  have hD0 : 0 < D := by linarith
  have hB : 0 ≤ 48 * (m : ℝ) / D := by positivity
  have hb := (sq_le_sq₀ hB hepsilon).mpr hbackground
  have hk : 0 ≤ Coulomb.kinetic state := Coulomb.kinetic_nonneg state
  have hm : 0 ≤ Coulomb.mass state := Coulomb.mass_nonneg state
  have hkin := mul_le_mul_of_nonneg_right (add_le_add hp hs) hk
  have hmass := mul_le_mul_of_nonneg_right hb hm
  apply (isolatedPerturbation_norm_bound hD hq hq1 hq' hq'1 center displacement hdisp site state).trans
  nlinarith

end ContinuumCoulomb

end

end OAI

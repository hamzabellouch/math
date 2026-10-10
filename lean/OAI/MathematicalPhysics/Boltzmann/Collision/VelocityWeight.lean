import OAI.MathematicalPhysics.Boltzmann.Collision.FourierL2Identification
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

section

/-! # Removing a countable family of velocity windows from a null-set statement -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem ae_prod_of_velocity_windows {P : X × Velocity → Prop}
    (h : ∀ n : ℕ, ∀ᵐ z ∂μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ))), P z) :
    ∀ᵐ z ∂μ.prod (volume : Measure Velocity), P z := by
  have he : (⋃ n : ℕ, (univ : Set X) ×ˢ Metric.closedBall (0:Velocity) (n:ℝ)) = univ := by
    rw [← prod_iUnion,Metric.iUnion_closedBall_nat,univ_prod_univ]
  have hh := (ae_restrict_iUnion_iff (μ := μ.prod (volume : Measure Velocity))
    (fun n : ℕ => (univ : Set X) ×ˢ Metric.closedBall (0:Velocity) (n:ℝ)) P).mpr (fun n => by
      rw [← Measure.prod_restrict,Measure.restrict_univ]
      exact h n)
  simpa only [he,Measure.restrict_univ] using hh

end BoltzmannNonuniqueness

end

end

section

/-!
# The transverse singularity in the velocity majorant

Section 3 uses `H(v) = exp(-‖v‖²) * ⟨v⟩^(-100) * (1 + ‖v̄‖^(-q))`.
Thus its polynomial factor is `(1 + ‖v‖²)^(-50)`. The values assigned on
the velocity axis use Mathlib's real-power convention and do not affect
Lebesgue integrability.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.VelocityWeight

abbrev Transverse := EuclideanSpace ℝ (Fin 2)

def transverse (v : Velocity) : Transverse :=
  WithLp.toLp 2 (fun i : Fin 2 => v i.castSucc)

def axial (v : Velocity) : ℝ := v (Fin.last 2)

def singularity (q : ℝ) (u : Transverse) : ℝ := ‖u‖ ^ (-q)

def H (q : ℝ) (v : Velocity) : ℝ :=
  Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) *
    (1 + singularity q (transverse v))

/-- The coordinate split is first axial, then transverse. -/
def split : Velocity ≃ᵐ (ℝ × Transverse) :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

theorem split_apply (v : Velocity) : split v = (axial v, transverse v) := by
  apply Prod.ext
  · rfl
  · apply (WithLp.ext_iff 2).mpr
    funext i
    change v ((Fin.last 2).succAbove i) = v i.castSucc
    rw [Fin.succAbove_last]

theorem split_measurePreserving : MeasurePreserving split := by
  have h₁ := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin 2))
  exact (h₁.trans h₂).trans h₃

theorem norm_sq_split (v : Velocity) :
    ‖v‖ ^ 2 = ‖transverse v‖ ^ 2 + (axial v) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [transverse, axial, PiLp.toLp_apply]
  exact Fin.sum_univ_castSucc (fun i : Fin 3 => v i ^ 2)

theorem singularity_nonneg (q : ℝ) (u : Transverse) : 0 ≤ singularity q u :=
  Real.rpow_nonneg (norm_nonneg _) _

/-- The sharp local integrability range includes the manuscript's `1 < q < 2`. -/
theorem locallyIntegrable_singularity {q : ℝ} (hq : q < 2) :
    LocallyIntegrable (singularity q) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := q)
    (by simp) (by simpa using hq)
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (singularity_nonneg q u)]
    simp only [singularity, one_mul, le_refl]
  · unfold singularity
    exact (measurable_norm.pow measurable_const).aestronglyMeasurable

/-- Gaussian decay retains transverse powers whenever their exponent exceeds `-2`. -/
theorem integrable_transverse_gaussian_rpow {β s : ℝ} (hβ : 0 < β) (hs : -2 < s) :
    Integrable (fun u : Transverse => ‖u‖ ^ s * Real.exp (-β * ‖u‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Transverse)
    (f := fun r : ℝ => r ^ s * Real.exp (-β * r ^ 2))).mpr
  have hi : IntegrableOn (fun r : ℝ => r ^ (s + 1) * Real.exp (-β * r ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hβ (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  rw [Real.rpow_add hr' s 1, Real.rpow_one]
  ring

def gaussianMajorant (β q : ℝ) (v : Velocity) : ℝ :=
  Real.exp (-β * ‖v‖ ^ 2) * (1 + singularity q (transverse v))

theorem gaussianMajorant_nonneg (β q : ℝ) (v : Velocity) :
    0 ≤ gaussianMajorant β q v := by
  unfold gaussianMajorant singularity
  positivity

theorem integrable_gaussianMajorant {β q : ℝ} (hβ : 0 < β) (hq : q < 2) :
    Integrable (gaussianMajorant β q) := by
  have hb₀ : Integrable (fun u : Transverse => Real.exp (-β * ‖u‖ ^ 2)) := by
    simpa only [Real.rpow_zero, one_mul] using
      integrable_transverse_gaussian_rpow (s := 0) hβ (by norm_num)
  have hb₁ := integrable_transverse_gaussian_rpow (s := -q) hβ (by linarith)
  have hb : Integrable (fun u : Transverse =>
      (1 + singularity q u) * Real.exp (-β * ‖u‖ ^ 2)) := by
    convert hb₀.add hb₁ using 1
    funext u
    simp only [singularity, Pi.add_apply]
    ring
  have ha := integrable_exp_neg_mul_sq hβ
  have hp := ha.mul_prod hb
  have hc := split_measurePreserving.integrable_comp_of_integrable hp
  convert hc using 1
  funext v
  simp only [gaussianMajorant, Function.comp_apply, split_apply]
  have he : Real.exp (-β * ‖v‖ ^ 2) =
      Real.exp (-β * ‖transverse v‖ ^ 2) * Real.exp (-β * (axial v) ^ 2) := by
    rw [norm_sq_split, mul_add, Real.exp_add]
  rw [he]
  ring

theorem H_nonneg (q : ℝ) (v : Velocity) : 0 ≤ H q v := by
  unfold H singularity
  positivity

theorem H_le_gaussianMajorant (q : ℝ) (v : Velocity) :
    H q v ≤ gaussianMajorant 1 q v := by
  have hp : (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
  unfold H gaussianMajorant
  simp only [neg_mul, one_mul]
  have hw : 0 ≤ 1 + singularity q (transverse v) :=
    add_nonneg zero_le_one (singularity_nonneg q (transverse v))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hw

theorem integrable_H {q : ℝ} (hq : q < 2) : Integrable (H q) := by
  apply (integrable_gaussianMajorant zero_lt_one hq).mono'
  · unfold H singularity transverse
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg q v)]
    exact H_le_gaussianMajorant q v

theorem H_pos (q : ℝ) (v : Velocity) : 0 < H q v := by
  unfold H
  apply mul_pos
  · exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  · linarith [singularity_nonneg q (transverse v)]

/-- Absorbing an even power into half the Gaussian decay gives an explicit factorial constant. -/
theorem even_pow_mul_gaussian_le (r : ℝ) (n : ℕ) :
    r ^ (2 * n) * Real.exp (-r ^ 2) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-r ^ 2 / 2) := by
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have hpow : (r ^ 2 / 2) ^ n ≤ Real.exp (r ^ 2 / 2) * (n.factorial : ℝ) :=
    (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (r ^ 2 / 2) (by positivity) n)
  have hid : r ^ (2 * n) = (2 : ℝ) ^ n * (r ^ 2 / 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  calc
    r ^ (2 * n) * Real.exp (-r ^ 2) =
        (2 : ℝ) ^ n * (r ^ 2 / 2) ^ n * Real.exp (-r ^ 2) := by rw [hid]
    _ ≤ (2 : ℝ) ^ n * (Real.exp (r ^ 2 / 2) * (n.factorial : ℝ)) *
        Real.exp (-r ^ 2) := by gcongr
    _ = (2 : ℝ) ^ n * (n.factorial : ℝ) *
        (Real.exp (r ^ 2 / 2) * Real.exp (-r ^ 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem H_even_moment_le (q : ℝ) (v : Velocity) (n : ℕ) :
    ‖v‖ ^ (2 * n) * H q v ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * gaussianMajorant (1 / 2) q v := by
  have hw : 0 ≤ 1 + singularity q (transverse v) :=
    add_nonneg zero_le_one (singularity_nonneg q (transverse v))
  calc
    ‖v‖ ^ (2 * n) * H q v ≤ ‖v‖ ^ (2 * n) * gaussianMajorant 1 q v :=
      mul_le_mul_of_nonneg_left (H_le_gaussianMajorant q v) (pow_nonneg (norm_nonneg _) _)
    _ = (‖v‖ ^ (2 * n) * Real.exp (-‖v‖ ^ 2)) *
        (1 + singularity q (transverse v)) := by
      simp only [gaussianMajorant, neg_mul, one_mul]
      ring
    _ ≤ ((2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-‖v‖ ^ 2 / 2)) *
        (1 + singularity q (transverse v)) :=
      mul_le_mul_of_nonneg_right (even_pow_mul_gaussian_le ‖v‖ n) hw
    _ = _ := by
      unfold gaussianMajorant
      rw [show -(1 / 2 : ℝ) * ‖v‖ ^ 2 = -‖v‖ ^ 2 / 2 by ring]
      ring

theorem integrable_even_moment_H {q : ℝ} (hq : q < 2) (n : ℕ) :
    Integrable (fun v : Velocity => ‖v‖ ^ (2 * n) * H q v) := by
  have hb := (integrable_gaussianMajorant (β := 1 / 2) (by norm_num) hq).const_mul
    ((2 : ℝ) ^ n * (n.factorial : ℝ))
  have hn : AEStronglyMeasurable (fun v : Velocity => ‖v‖ ^ (2 * n)) := by fun_prop
  apply hb.mono' (hn.mul (integrable_H hq).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Pi.mul_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (H_nonneg q v))]
  exact H_even_moment_le q v n

/-- The majorant has every natural polynomial velocity moment. -/
theorem integrable_moment_H {q : ℝ} (hq : q < 2) (n : ℕ) :
    Integrable (fun v : Velocity => ‖v‖ ^ n * H q v) := by
  have hn : AEStronglyMeasurable (fun v : Velocity => ‖v‖ ^ n) := by fun_prop
  apply ((integrable_H hq).add (integrable_even_moment_H hq n)).mono'
    (hn.mul (integrable_H hq).aestronglyMeasurable)
  filter_upwards [] with v
  have hpow : ‖v‖ ^ n ≤ 1 + ‖v‖ ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul]
    nlinarith [sq_nonneg (‖v‖ ^ n - (1 / 2 : ℝ))]
  rw [Pi.mul_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (H_nonneg q v))]
  calc
    ‖v‖ ^ n * H q v ≤ (1 + ‖v‖ ^ (2 * n)) * H q v :=
      mul_le_mul_of_nonneg_right hpow (H_nonneg q v)
    _ = _ := by simp only [Pi.add_apply]; ring

private theorem one_add_rpow_le {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) :
    (1 + s) ^ p ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
  by_cases hs₁ : s ≤ 1
  · calc
      (1 + s) ^ p ≤ (2 : ℝ) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        have hs' : 0 ≤ s ^ p := Real.rpow_nonneg hs p
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 1 + s ^ p from le_add_of_nonneg_right hs')
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
  · have hs₁' : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
    calc
      (1 + s) ^ p ≤ (2 * s) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = (2 : ℝ) ^ p * s ^ p := Real.mul_rpow (by norm_num) hs
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
          (Real.rpow_nonneg (by norm_num) p)

/-- Raising the majorant to a positive power multiplies its transverse singular exponent. -/
theorem H_rpow_le {p : ℝ} (hp : 0 ≤ p) (q : ℝ) (v : Velocity) :
    H q v ^ p ≤ (2 : ℝ) ^ p * gaussianMajorant p (p * q) v := by
  have hs : 0 ≤ singularity q (transverse v) := singularity_nonneg q (transverse v)
  have he : Real.exp (-‖v‖ ^ 2) ^ p = Real.exp (-p * ‖v‖ ^ 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hr : singularity q (transverse v) ^ p = singularity (p * q) (transverse v) := by
    unfold singularity
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  calc
    H q v ^ p ≤ gaussianMajorant 1 q v ^ p :=
      Real.rpow_le_rpow (H_nonneg q v) (H_le_gaussianMajorant q v) hp
    _ = Real.exp (-p * ‖v‖ ^ 2) * (1 + singularity q (transverse v)) ^ p := by
      unfold gaussianMajorant
      simp only [neg_mul, one_mul]
      rw [Real.mul_rpow (Real.exp_nonneg _) (by positivity), he]
      simp only [neg_mul]
    _ ≤ Real.exp (-p * ‖v‖ ^ 2) *
        ((2 : ℝ) ^ p * (1 + singularity q (transverse v) ^ p)) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le hs hp) (Real.exp_nonneg _)
    _ = _ := by rw [hr]; unfold gaussianMajorant; ring

/-- The precise power-integrability range used for the initial cutoff solutions. -/
theorem integrable_rpow_H {p q : ℝ} (hp : 1 ≤ p) (hpq : p * q < 2) :
    Integrable (fun v : Velocity => H q v ^ p) := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_nonneg : 0 ≤ p := hp₀.le
  have hm : AEStronglyMeasurable (fun v : Velocity => H q v ^ p) := by
    unfold H singularity transverse
    fun_prop
  apply ((integrable_gaussianMajorant hp₀ hpq).const_mul ((2 : ℝ) ^ p)).mono' hm
  filter_upwards [] with v
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (H_nonneg q v) p)]
  exact H_rpow_le hp₀.le q v

theorem exists_integrable_rpow_H {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ p : ℝ, 1 < p ∧ Integrable (fun v : Velocity => H q v ^ p) := by
  have hq₀ : 0 < q := lt_trans zero_lt_one hq₁
  have hdiv : (1 : ℝ) < 2 / q := (lt_div_iff₀ hq₀).mpr (by simpa using hq₂)
  obtain ⟨p, hp₁, hp₂⟩ := exists_between hdiv
  exact ⟨p, hp₁, integrable_rpow_H hp₁.le ((lt_div_iff₀ hq₀).mp hp₂)⟩

end BoltzmannNonuniqueness.VelocityWeight

end

end

section

/-! # Plancherel energy for the partial Fourier transform in spacetime -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

def velocityFourier (r : Velocity × FourierSpace → ℂ) (p : Velocity × FourierSpace) : ℂ :=
  𝓕 (fun x => r (p.1,x)) p.2

theorem velocityFourier_measurable {r : Velocity × FourierSpace → ℂ} (hr : Measurable r) :
    Measurable (velocityFourier r) := by
  have hm : Measurable (fun p : (Velocity × FourierSpace) × FourierSpace =>
      𝐞 (-inner ℝ p.2 p.1.2) • r (p.1.1,p.2)) := by
    have hc : Measurable (fun p : (Velocity × FourierSpace) × FourierSpace =>
        𝐞 (-inner ℝ p.2 p.1.2)) := by fun_prop
    exact hc.smul (hr.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

attribute [local irreducible] velocityFourier

theorem velocityFourier_fiber_energy {r : Velocity × FourierSpace → ℂ}
    (v : Velocity) (h₁ : Integrable (fun x => r (v,x)))
    (h₂ : MemLp (fun x => r (v,x)) 2 volume) :
    (∫ x : FourierSpace, ‖velocityFourier r (v,x)‖^2) = ∫ x : FourierSpace, ‖r (v,x)‖^2 :=
  by simpa only [velocityFourier] using fourier_integral_norm_sq h₁ h₂

theorem velocityFourier_fiber_memLp {r : Velocity × FourierSpace → ℂ}
    (v : Velocity) (h₁ : Integrable (fun x => r (v,x)))
    (h₂ : MemLp (fun x => r (v,x)) 2 volume) :
    MemLp (fun x => velocityFourier r (v,x)) 2 volume :=
  by simpa only [velocityFourier] using fourier_integral_memLp h₁ h₂

theorem velocityFourier_integrable_sq {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) :
    Integrable (fun p => ‖velocityFourier r p‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂
  have hm : Measurable (fun p => ‖velocityFourier r p‖^2) :=
    (velocityFourier_measurable hr).norm.pow_const 2
  have hfiber : ∀ᵐ v ∂(volume : Measure Velocity),
      MemLp (fun x => r (v,x)) 2 volume := by
    filter_upwards [hi.prod_right_ae] with v hv
    have hmv : Measurable (fun x : FourierSpace => r (v,x)) := hr.comp measurable_prodMk_left
    exact (memLp_two_iff_integrable_sq_norm hmv.aestronglyMeasurable).mpr hv
  have he : ∀ᵐ v ∂(volume : Measure Velocity),
      (∫ x : FourierSpace, ‖velocityFourier r (v,x)‖^2) =
        ∫ x : FourierSpace, ‖r (v,x)‖^2 := by
    filter_upwards [h₁.prod_right_ae,hfiber] with v hv₁ hv₂
    exact velocityFourier_fiber_energy v hv₁ hv₂
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [h₁.prod_right_ae,hfiber] with v hv₁ hv₂
    have hv := velocityFourier_fiber_memLp v hv₁ hv₂
    exact (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  · apply hi.integral_norm_prod_left.congr
    filter_upwards [he] with v hv
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hv.symm

theorem velocityFourier_energy {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) :
    (∫ p, ‖velocityFourier r p‖^2) = ∫ p, ‖r p‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂
  change (∫ p, ‖velocityFourier r p‖^2 ∂(volume.prod volume)) =
    ∫ p, ‖r p‖^2 ∂(volume.prod volume)
  rw [integral_prod _ (velocityFourier_integrable_sq hr h₁ h₂),integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [h₁.prod_right_ae,hi.prod_right_ae] with v hv₁ hv₂
  have hmv : Measurable (fun x : FourierSpace => r (v,x)) := hr.comp measurable_prodMk_left
  exact velocityFourier_fiber_energy v hv₁
    ((memLp_two_iff_integrable_sq_norm hmv.aestronglyMeasurable).mpr hv₂)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Velocity support is preserved by the partial spacetime Fourier transform -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem velocityFourier_support {r : Velocity × FourierSpace → ℂ} {R : ℝ}
    (hs : ∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) :
    ∀ᵐ v ∂(volume : Measure Velocity), R < ‖v‖ →
      ∀ k, velocityFourier r (v,k) = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with v hv
  intro hR k
  have hz : (fun x : FourierSpace => r (v,x)) =ᵐ[volume] 0 := by
    filter_upwards [hv] with x hx
    exact hx hR
  calc
    _ = 𝓕 (0 : FourierSpace → ℂ) k := Real.fourier_congr_ae hz k
    _ = 0 := by rw [Real.fourier_eq]; simp

end BoltzmannNonuniqueness.Published

end

end

end OAI

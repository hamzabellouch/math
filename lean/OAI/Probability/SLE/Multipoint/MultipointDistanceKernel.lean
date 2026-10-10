import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace OAI

/-! The local planar singularities used to integrate the capped distance
kernel. Diagonal values are set to zero; they have zero planar measure. -/

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

def distanceKernel (α : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x y ^ (-α))

lemma distanceKernel_symm (α : ℝ) (x y : ℂ) :
    distanceKernel α x y = distanceKernel α y x := by
  simp only [distanceKernel,dist_comm]

@[fun_prop]
lemma measurable_distanceKernel (α : ℝ) :
    Measurable (fun p : ℂ × ℂ => distanceKernel α p.1 p.2) := by
  unfold distanceKernel
  fun_prop

lemma measurable_distanceKernel_left (α : ℝ) (y : ℂ) :
    Measurable (fun x : ℂ => distanceKernel α x y) := by
  unfold distanceKernel
  fun_prop

def radialKernelMass (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℂ in ball 0 1, ENNReal.ofReal (‖x‖ ^ (-α))

lemma radialKernelMass_lt_top {α : ℝ} (hα : α < 2) : radialKernelMass α < ⊤ := by
  have hi : IntegrableOn (fun x : ℂ => ‖x‖ ^ (-α)) (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1)
      (α := α) (by simp [Complex.finrank_real_complex])
      (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hα)
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul]
    · exact ((continuous_norm.measurable).pow_const _).aestronglyMeasurable
  exact (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) _))).mp hi.hasFiniteIntegral

lemma distanceKernel_le_local_add_one {α : ℝ} (hα : 0 ≤ α) (x y : ℂ) :
    distanceKernel α x y ≤
      (ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-α))) (x-y) + 1 := by
  by_cases h : x-y ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem h]
    simpa only [distanceKernel,dist_eq_norm] using
      (le_add_right (le_refl (ENNReal.ofReal (‖x-y‖ ^ (-α)))))
  · rw [indicator_of_notMem h,zero_add]
    have hd : 1 ≤ dist x y := by
      simpa only [mem_ball_zero_iff,not_lt,← dist_eq_norm] using h
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos hd (neg_nonpos.mpr hα))

theorem distanceKernel_lintegral_le {α : ℝ} (hα : 0 ≤ α)
    (K : Set ℂ) (y : ℂ) :
    (∫⁻ x in K, distanceKernel α x y) ≤ radialKernelMass α + volume K := by
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator
    (fun z => ENNReal.ofReal (‖z‖ ^ (-α)))
  have hfm : Measurable f := by
    apply Measurable.indicator _ measurableSet_ball
    fun_prop
  have hshiftm : Measurable (fun x : ℂ => f (x-y)) :=
    hfm.comp (measurable_id.sub_const y)
  calc
    (∫⁻ x in K, distanceKernel α x y) ≤ ∫⁻ x in K, f (x-y)+1 :=
      lintegral_mono (distanceKernel_le_local_add_one hα · y)
    _ = (∫⁻ x in K, f (x-y)) + volume K := by
      rw [lintegral_add_left hshiftm,lintegral_const]
      simp only [Measure.restrict_apply_univ,one_mul]
    _ ≤ (∫⁻ x, f (x-y)) + volume K :=
      add_le_add (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)) le_rfl
    _ = radialKernelMass α + volume K := by
      rw [lintegral_sub_right_eq_self]
      simp only [f,lintegral_indicator measurableSet_ball,radialKernelMass]

lemma distanceKernel_mul_le_squares (α : ℝ) (x y z : ℂ) :
    distanceKernel α x y * distanceKernel α x z ≤
      distanceKernel (2*α) x y + distanceKernel (2*α) x z := by
  have hs (w : ℂ) : (dist x w ^ (-α))^2 = dist x w ^ (-(2*α)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul dist_nonneg]
    congr 1
    ring
  unfold distanceKernel
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg _),
    ← ENNReal.ofReal_add (Real.rpow_nonneg dist_nonneg _) (Real.rpow_nonneg dist_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← hs y,← hs z]
  nlinarith [sq_nonneg ((dist x y ^ (-α))-(dist x z ^ (-α)))]

theorem distanceKernel_pair_lintegral_le {α : ℝ} (hα : 0 ≤ α)
    (K : Set ℂ) (y z : ℂ) :
    (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤
      2*(radialKernelMass (2*α)+volume K) := by
  calc
    (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤
        ∫⁻ x in K, distanceKernel (2*α) x y + distanceKernel (2*α) x z :=
      lintegral_mono (distanceKernel_mul_le_squares α · y z)
    _ = (∫⁻ x in K, distanceKernel (2*α) x y) +
        (∫⁻ x in K, distanceKernel (2*α) x z) := by
      apply lintegral_add_left
      exact measurable_distanceKernel_left (2*α) y
    _ ≤ (radialKernelMass (2*α)+volume K)+(radialKernelMass (2*α)+volume K) :=
      add_le_add (distanceKernel_lintegral_le (by positivity) K y)
        (distanceKernel_lintegral_le (by positivity) K z)
    _ = _ := (two_mul _).symm

theorem distanceKernel_uniform_local_bounds {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ 1 ≤ C ∧ volume K ≤ C ∧
      (∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C) ∧
      (∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C) := by
  let C := 1+volume K+(radialKernelMass α+volume K)+2*(radialKernelMass (2*α)+volume K)
  have hvol : volume K < ⊤ := hK.measure_lt_top
  have hmass : radialKernelMass α < ⊤ := radialKernelMass_lt_top (by linarith)
  have hmass2 : radialKernelMass (2*α) < ⊤ := radialKernelMass_lt_top (by linarith)
  refine ⟨C,by dsimp [C]; finiteness,?_,?_,?_,?_⟩
  · dsimp [C]
    exact (le_add_right le_rfl).trans ((le_add_right le_rfl).trans (le_add_right le_rfl))
  · dsimp [C]
    exact (le_add_left le_rfl).trans ((le_add_right le_rfl).trans (le_add_right le_rfl))
  · intro y
    exact (distanceKernel_lintegral_le hα.le K y).trans
      ((le_add_left le_rfl).trans (le_add_right le_rfl))
  · intro y z
    exact (distanceKernel_pair_lintegral_le hα.le K y z).trans (le_add_left le_rfl)

end SLEExactGauge.Multipoint

end

end OAI

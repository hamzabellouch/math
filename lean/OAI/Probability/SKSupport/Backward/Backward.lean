import Mathlib
import OAI.Probability.SKSupport.Foundations.DerivWithinVarianceHeatWeightExp

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backward (c T : ℝ) (f : ℝ → ℝ) (t x : ℝ) := varianceLogHeat c (T-t) f x

def backwardRate (c T : ℝ) (f : ℝ → ℝ) (t x : ℝ) :=
  -(1/2:ℝ)*varianceTilted c (T-t) f (generatorWeight c f) x

lemma backward_terminal (c T : ℝ) (f : ℝ → ℝ) (x : ℝ) : backward c T f T x = f x := by
  unfold backward
  rw [sub_self]
  by_cases hc : c = 0
  · simp [varianceLogHeat, hc, varianceHeat_zero]
  · simp [varianceLogHeat, hc, varianceHeat_zero, Real.log_exp, mul_div_cancel_left₀ _ hc]

structure VerificationData (F D : ℝ → ℝ → ℝ) (c T : ℝ) : Prop where
  smooth : ∀ t, ContDiff ℝ 3 (F t)
  gradient_bound : ∀ t z, |deriv (F t) z| ≤ 1
  bounds : ∃ C₂ C₃ Ct L : ℝ≥0,
    (∀ t z, |deriv (deriv (F t)) z| ≤ C₂) ∧
    (∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃) ∧
    (∀ t, Measurable (D t)) ∧
    (∀ t z, |D t z| ≤ Ct) ∧
    (∀ r ∈ Set.Icc (0:ℝ) T, ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc (0:ℝ) T) r) ∧
    (∀ r ∈ Set.Icc (0:ℝ) T, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) T, ∀ z,
      D t z+(1/2:ℝ)*deriv (deriv (F t)) z+c/2*(deriv (F t) z)^2 = 0)

lemma backward_verificationData {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    VerificationData (backward c T f) (backwardRate c T f) c T := by
  have hw := boundedSmooth_generatorWeight hf c
  obtain ⟨C₂,hC₂⟩ := uniform_varianceLogHeat_derivative_bounds hf hLip hc 1
  obtain ⟨C₃,hC₃⟩ := uniform_varianceLogHeat_derivative_bounds hf hLip hc 2
  obtain ⟨G,hG⟩ := hw.bound
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hw hc
  obtain ⟨A,hA⟩ := varianceTilted_space_lipschitz hf hLip hw hc
  constructor
  · intro t
    exact (regularDatum_varianceLogHeat hf hLip hc (T-t)).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t z
    exact norm_deriv_le_of_lipschitz (varianceLogHeat_lipschitz hLip hc (T-t))
  · refine ⟨C₂,C₃,G/2,L,?_,?_,?_,?_,?_,?_,?_⟩
    · intro t z
      change |deriv (deriv (varianceLogHeat c (T-t) f)) z| ≤ C₂
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hC₂ (T-t) z
    · intro t z
      exact hC₃ (T-t) z
    · intro t
      exact measurable_const.mul (hA (T-t)).continuous.measurable
    · intro t z
      dsimp only [backwardRate]
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      have hb := varianceTilted_bound hLip hw.smooth.continuous.measurable hG c (T-t) z
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    · intro r hr z
      have hd := (varianceLogHeat_time_derivative hf hLip c (sub_nonneg.mpr hr.2) z).comp r
        (((hasDerivAt_const r T).sub (hasDerivAt_id r)).hasDerivWithinAt (s := Set.Icc (0:ℝ) T))
        (fun (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) T) => show 0 ≤ T-s from sub_nonneg.mpr hs.2)
      convert hd using 1 <;> try rfl
      dsimp only [backwardRate]
      ring
    · intro r hr s hs z y
      have hb := hL (T-r) (sub_nonneg.mpr hr.2) (T-s) (sub_nonneg.mpr hs.2) z y
      have he : |(T-r)-(T-s)| = |r-s| := by
        rw [show (T-r)-(T-s) = -(r-s) by ring, abs_neg]
      rw [he] at hb
      dsimp only [backwardRate]
      rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      have hn := abs_nonneg (varianceTilted c (T-r) f (generatorWeight c f) z-
        varianceTilted c (T-s) f (generatorWeight c f) y)
      linarith
    · intro t ht z
      have he := varianceLogHeat_generator_identity hf hLip c (sub_nonneg.mpr ht.2) z
      change -(1/2:ℝ)*varianceTilted c (T-t) f (generatorWeight c f) z+
        (1/2:ℝ)*deriv (deriv (varianceLogHeat c (T-t) f)) z+
        c/2*(deriv (varianceLogHeat c (T-t) f) z)^2 = 0
      linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI

import OAI.MeasureTheory.Falconer.Measures.ConditionalFrostman
import OAI.MeasureTheory.Falconer.Fourier.FourierLebesgue
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! # Gaussian mass at a finite Frostman scale

Only ball bounds at radii at least `B⁻¹` are used. This is the spatial
Gaussian estimate in the proof of the half-dimensional Fourier estimate.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def gaussianBallConstant (k : ℕ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(n:ℝ))*((n:ℝ)+1)^k

theorem gaussianBallConstant_summable (k : ℕ) :
    Summable (fun n : ℕ => Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul k (r := 1) zero_lt_one)
  have he (n : ℕ) : Real.exp (-(n:ℝ))*((n:ℝ)+1)^k =
      Real.exp 1 * (((n+1:ℕ):ℝ)^k*Real.exp (-1*((n+1:ℕ):ℝ))) := by
    have he' : Real.exp 1*Real.exp (-1*((n+1:ℕ):ℝ)) = Real.exp (-(n:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [← he']
    push_cast
    ring
  simpa only [he] using h.mul_left (Real.exp 1)

theorem gaussianBallConstant_nonneg (k : ℕ) : 0 ≤ gaussianBallConstant k :=
  tsum_nonneg (fun n => by positivity)

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def gaussianMassTerm (x : X) (B : ℝ) (n : ℕ) : X → ℝ≥0∞ :=
  (ball x (((n:ℝ)+1)/B)).indicator (fun _ => ENNReal.ofReal (Real.exp (-(n:ℝ))))

omit [MeasurableSpace X] [BorelSpace X] in
theorem gaussian_pointwise_majorant {B : ℝ} (hB : 0 < B) (x y : X) :
    ENNReal.ofReal (Real.exp (-(B*dist x y)^2)) ≤
      ∑' n : ℕ, gaussianMassTerm x B n y := by
  let n := Nat.floor (B*dist x y)
  have hn : (n:ℝ) ≤ B*dist x y := Nat.floor_le (by positivity)
  have hn' : B*dist x y < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hball : y ∈ ball x (((n:ℝ)+1)/B) := by
    rw [mem_ball,dist_comm,lt_div_iff₀ hB]
    simpa only [mul_comm] using hn'
  have hsq : (n:ℝ) ≤ (n:ℝ)^2 := by
    have hh : n ≤ n^2 := by nlinarith
    exact_mod_cast hh
  have hle : Real.exp (-(B*dist x y)^2) ≤ Real.exp (-(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (B*dist x y-(n:ℝ))]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ))) := ENNReal.ofReal_le_ofReal hle
    _ = gaussianMassTerm x B n y := by
      rw [gaussianMassTerm,indicator_of_mem hball]
    _ ≤ _ := ENNReal.le_tsum (f := fun j => gaussianMassTerm x B j y) n

theorem gaussian_mass_bound (μ : Measure X) {B K s : ℝ} {k : ℕ}
    (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : X, ∀ r : ℝ, 1/B ≤ r → μ (ball x r) ≤ ENNReal.ofReal (K*r^s))
    (x : X) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-(B*dist x y)^2)) ∂μ) ≤
      ENNReal.ofReal (K*(1/B)^s*gaussianBallConstant k) := by
  have hterm (n : ℕ) : (∫⁻ y, gaussianMassTerm x B n y ∂μ) ≤
      ENNReal.ofReal (K*(1/B)^s) *
        ENNReal.ofReal (Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := by
    rw [gaussianMassTerm,lintegral_indicator_const measurableSet_ball]
    have hr : 1/B ≤ ((n:ℝ)+1)/B := by
      exact (div_le_div_iff_of_pos_right hB).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hp : (((n:ℝ)+1)/B)^s ≤ (1/B)^s*((n:ℝ)+1)^k := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (inv_nonneg.mpr hB.le),one_div]
      have hh : ((n:ℝ)+1)^s ≤ ((n:ℝ)+1)^(k:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) hsk
      rw [Real.rpow_natCast] at hh
      nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hB.le) s]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ)))*ENNReal.ofReal (K*(((n:ℝ)+1)/B)^s) :=
        mul_le_mul_right (hb x _ hr) _
      _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ)))*
          ENNReal.ofReal (K*((1/B)^s*((n:ℝ)+1)^k)) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  calc
    _ ≤ ∫⁻ y, ∑' n : ℕ, gaussianMassTerm x B n y ∂μ :=
      lintegral_mono (gaussian_pointwise_majorant hB x)
    _ = ∑' n : ℕ, ∫⁻ y, gaussianMassTerm x B n y ∂μ :=
      lintegral_tsum (fun n => (measurable_const.indicator measurableSet_ball).aemeasurable)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (K*(1/B)^s)*
        ENNReal.ofReal (Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := ENNReal.tsum_le_tsum hterm
    _ = _ := by
      rw [ENNReal.tsum_mul_left,← ENNReal.ofReal_tsum_of_nonneg
        (fun n : ℕ => by positivity) (gaussianBallConstant_summable k),
        ← ENNReal.ofReal_mul (by positivity)]
      rfl

end Falconer

end OAI

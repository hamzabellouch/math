import OAI.Geometry.RCD.Heat.CanonicalPowerLower

namespace OAI

/-! # A global Gaussian lower rate at short times

The number of near-diagonal steps grows linearly in squared distance over
time. The resulting power bound gives a genuine exponential lower rate.
No sharp value of the exponent is needed for the logarithmic estimates.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_rough_gaussian_lower :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x y : X,
      c/(hausdorff n X).real (ball y (Real.sqrt t)) * Real.exp (-D*(dist x y)^2/t) ≤
        hX.canonicalHeatKernel hn p t x y := by
  obtain ⟨b,hb,hb1,hpow⟩ := hX.canonicalHeatKernel_power_lower hn p
  let D := -4*Real.log b
  have hlog : Real.log b < 0 := Real.log_neg hb hb1
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨b,D,hb,hD,?_⟩
  intro t ht ht1 x y
  let A := 4*(dist x y)^2/t
  let N := ⌊A⌋₊+1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hNpos : 0 < N := Nat.succ_pos _
  have hAN : A < (N:ℝ) := by exact_mod_cast Nat.lt_floor_add_one A
  have hNA : (N:ℝ) ≤ A+1 := by
    dsimp only [N]
    push_cast
    linarith only [Nat.floor_le hA]
  have hd : (dist x y)^2 ≤ (N:ℝ)*t/4 := by
    have hh := (div_lt_iff₀ ht).mp hAN
    nlinarith only [hh]
  have hrate : b*Real.exp (-D*(dist x y)^2/t) ≤ b^N := by
    calc
      _ = Real.exp ((A+1)*Real.log b) := by
        have he : (A+1)*Real.log b = Real.log b + (-D*(dist x y)^2/t) := by
          dsimp only [A,D]
          ring
        rw [he,Real.exp_add,Real.exp_log hb]
      _ ≤ Real.exp ((N:ℝ)*Real.log b) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hNA hlog.le)
      _ = b^N := by rw [← Real.log_pow,Real.exp_log (pow_pos hb N)]
  have hV : 0 < (hausdorff n X).real (ball y (Real.sqrt t)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (Real.sqrt_pos.mpr ht)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  calc
    _ = (b*Real.exp (-D*(dist x y)^2/t))/(hausdorff n X).real (ball y (Real.sqrt t)) := by ring
    _ ≤ b^N/(hausdorff n X).real (ball y (Real.sqrt t)) := div_le_div_of_nonneg_right hrate hV.le
    _ ≤ _ := hpow N hNpos t ht ht1 x y hd

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

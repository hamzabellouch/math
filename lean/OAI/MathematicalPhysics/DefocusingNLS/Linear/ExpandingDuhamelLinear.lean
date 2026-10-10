import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamel

namespace OAI

/-! # Linearity of the moving-scale inhomogeneous term -/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

@[simp] theorem expandingDuhamel_zero (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (t : ℝ) :
    expandingDuhamel a b k L ha hk hL t (fun _ => 0) = 0 := by
  unfold expandingDuhamel
  have hz : expandingDuhamelIntegrand a b k L ha hk hL t (fun _ => 0) = 0 := by
    funext τ
    unfold expandingDuhamelIntegrand
    split_ifs <;> simp only [map_zero, Pi.zero_apply]
  simp only [hz, Pi.zero_apply, integral_zero]

theorem expandingDuhamel_add (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (r q : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t)) (hq : ContinuousOn q (Icc 0 t)) :
    expandingDuhamel a b k L ha hk hL t (fun τ => r τ + q τ) =
      expandingDuhamel a b k L ha hk hL t r +
        expandingDuhamel a b k L ha hk hL t q := by
  unfold expandingDuhamel
  rw [← integral_add (integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr)
    (integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t q hq)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ, map_add]

theorem expandingDuhamel_real_smul (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t c : ℝ) (r : ℝ → FourierL2) :
    expandingDuhamel a b k L ha hk hL t (fun τ => c • r τ) =
      c • expandingDuhamel a b k L ha hk hL t r := by
  unfold expandingDuhamel
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ,
    ContinuousLinearMap.map_smul_of_tower]

end DefocusingNLS

end OAI

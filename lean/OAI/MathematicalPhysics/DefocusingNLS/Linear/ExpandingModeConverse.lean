import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation

namespace OAI

/-! # The physical moving-mode equation implies the mild equation -/

open Set MeasureTheory

namespace DefocusingNLS

theorem hasDerivAt_expandingMode_interaction (a b L t : ℝ) (n : frequencyLattice)
    (c r : ℝ → ℂ)
    (hc : HasDerivAt c (expandingModeRate a b L t n * c t + r t) t) :
    HasDerivAt (fun s => (expandingFreeMode a b L s n)⁻¹ * c s)
      ((expandingFreeMode a b L t n)⁻¹ * r t) t := by
  have h := ((hasDerivAt_expandingFreeMode a b L t n).inv
    (expandingFreeMode_ne_zero a b L t n)).mul hc
  apply h.congr_deriv
  change -(expandingModeRate a b L t n * expandingFreeMode a b L t n) /
      expandingFreeMode a b L t n ^ 2 * c t +
      (expandingFreeMode a b L t n)⁻¹ * (expandingModeRate a b L t n * c t + r t) =
    (expandingFreeMode a b L t n)⁻¹ * r t
  field_simp [expandingFreeMode_ne_zero a b L t n]
  ring

theorem expandingMode_variation_of_constants (a b L T : ℝ) (n : frequencyLattice)
    (c r : ℝ → ℂ) (hc : ContinuousOn c (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hode : ∀ t ∈ Ioo 0 T, HasDerivAt c (expandingModeRate a b L t n * c t + r t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    c t = expandingFreeMode a b L t n *
      (c 0 + ∫ s in Icc 0 t, (expandingFreeMode a b L s n)⁻¹ * r s) := by
  have hinv : Continuous (fun s => (expandingFreeMode a b L s n)⁻¹) :=
    (continuous_expandingFreeMode a b L n).inv₀ (expandingFreeMode_ne_zero a b L · n)
  have hcont : ContinuousOn (fun s => (expandingFreeMode a b L s n)⁻¹ * c s) (Icc 0 t) :=
    hinv.continuousOn.mul (hc.mono (Icc_subset_Icc le_rfl ht.2))
  have hint : IntervalIntegrable (fun s => (expandingFreeMode a b L s n)⁻¹ * r s)
      volume 0 t :=
    (hinv.continuousOn.mul (hr.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont
    (fun s hs => hasDerivAt_expandingMode_interaction a b L s n c r
      (hode s ⟨hs.1, hs.2.trans_le ht.2⟩)) hint
  have hzero : expandingFreeMode a b L 0 n = 1 := by
    simp [expandingFreeMode, expandingFreeAmplitude, expandingFreeTime,
      schrodingerMultiplier]
  rw [hzero, inv_one, one_mul, intervalIntegral.integral_of_le ht.1,
    ← integral_Icc_eq_integral_Ioc] at he
  have hF := expandingFreeMode_ne_zero a b L t n
  calc
    c t = expandingFreeMode a b L t n * ((expandingFreeMode a b L t n)⁻¹ * c t) := by
      rw [← mul_assoc, mul_inv_cancel₀ hF, one_mul]
    _ = _ := by congr 1; exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)

/-- Equality of all physical coefficients identifies the actual vector path.
Only continuity at the slab endpoints is required there. -/
theorem expandingMild_of_mode_equation (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u r : ℝ → FourierL2) (hu : ContinuousOn u (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hode : ∀ t ∈ Ioo 0 T, ∀ n : frequencyLattice,
      HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n)
        (expandingModeRate a b L t n *
          expandingFourierCoefficient a k (expandingRadius L t) (u t) n +
          expandingFourierCoefficient a k (expandingRadius L t) (r t) n) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    u t = expandingFreeStep a b k L t ha hk hL ht.1 (u 0) +
      expandingDuhamel a b k L ha hk hL t r := by
  ext n
  have hR : 1 ≤ expandingRadius L t := hL.trans (expandingRadius_ge L t hL ht.1)
  rw [← weight_mul_expandingFourierCoefficient a k (expandingRadius L t) hR (u t) n,
    ← weight_mul_expandingFourierCoefficient a k (expandingRadius L t) hR
      (expandingFreeStep a b k L t ha hk hL ht.1 (u 0) +
        expandingDuhamel a b k L ha hk hL t r) n]
  congr 1
  rw [expandingMild_coefficient a b k L t ha hk hL ht.1 r
    (hr.mono (Icc_subset_Icc le_rfl ht.2)) (u 0) n]
  have he := expandingMode_variation_of_constants a b L T n
    (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n)
    (fun s => expandingFourierCoefficient a k (expandingRadius L s) (r s) n)
    (continuousOn_expandingPhysicalCoefficient a k L T hL u hu n)
    (continuousOn_expandingPhysicalCoefficient a k L T hL r hr n)
    (fun s hs => hode s hs n) t ht
  have hR0 : expandingRadius L 0 = L := by simp [expandingRadius]
  simpa only [hR0] using he

end DefocusingNLS

end OAI

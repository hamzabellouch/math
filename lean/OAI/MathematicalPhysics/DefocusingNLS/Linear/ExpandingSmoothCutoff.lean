import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothFilter
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFrequencyCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFrequencyCutoff

namespace OAI

/-! # Smooth frequency splitting with the actual commutator remainder bound -/

open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingSmoothLow (L R : ℝ) (hR : 0 < R) : FourierL2 →L[ℂ] FourierL2 :=
  fourierBoundedMultiplier 1 (by norm_num)
    (fun n : frequencyLattice => smoothFrequencyCutoff R hR (L⁻¹ • (n : E)))
    (fun _ => smoothFrequencyCutoff_norm_le R hR _)

@[simp] theorem expandingSmoothLow_apply (L R : ℝ) (hR : 0 < R)
    (f : FourierL2) (n : frequencyLattice) :
    expandingSmoothLow L R hR f n = smoothFrequencyCutoff R hR (L⁻¹ • (n : E)) * f n := rfl

noncomputable def expandingSmoothHigh (L R : ℝ) (hR : 0 < R) : FourierL2 →L[ℂ] FourierL2 :=
  ContinuousLinearMap.id ℂ FourierL2 - expandingSmoothLow L R hR

@[simp] theorem expandingSmoothHigh_apply (L R : ℝ) (hR : 0 < R)
    (f : FourierL2) (n : frequencyLattice) :
    expandingSmoothHigh L R hR f n =
      (1 - smoothFrequencyCutoff R hR (L⁻¹ • (n : E))) * f n := by
  change f n - smoothFrequencyCutoff R hR (L⁻¹ • (n : E)) * f n = _
  ring

theorem expandingSmoothHigh_norm_le (L R : ℝ) (hR : 0 < R) (f : FourierL2) :
    ‖expandingSmoothHigh L R hR f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [expandingSmoothHigh_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (one_sub_smoothFrequencyCutoff_norm_le R hR _)

theorem expandingSmoothHigh_low_zero (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (f : FourierL2) (n : frequencyLattice) (hn : ‖n‖ < R * L) :
    expandingSmoothHigh L R hR f n = 0 := by
  rw [expandingSmoothHigh_apply, smoothFrequencyCutoff_one]
  · ring
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), Submodule.norm_coe]
    have hh : ‖n‖ / L ≤ R := (div_le_iff₀ hL).mpr hn.le
    simpa only [div_eq_mul_inv, mul_comm] using hh

theorem expandingSmoothLow_eq_convolution (L R : ℝ) (hR : 0 < R) :
    expandingSmoothLow L R hR =
      expandingSchwartzFilter L (radianInverseKernel (smoothFrequencyCutoff R hR)) := by
  ext f n
  rw [expandingSmoothLow_apply, expandingSchwartzFilter_apply, radianFourierKernel_inverseKernel]

theorem exists_torusOddCommutator_smooth_remainder (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L) (hR : 1 ≤ R),
      let q := schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K
      ∀ (M : ℝ) (hM : 0 ≤ M)
        (hQB : ∀ x : UnitAddTorus (Fin 12), ‖expandingUnitTorusFunction a (N + 1 : ℕ) L q x‖ ^ (2 * m) ≤ M)
        (f : FourierL2) (j : Fin (N + 1) → Fin 12),
      ‖expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j f -
        expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j
          (expandingSmoothLow L R (by linarith) f)‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨C, hC, hc⟩ := exists_torusOddCommutator_high_bound a N ha ha1 hN m K
  refine ⟨C, hC, ?_⟩
  intro L R hL hR q M hM hQB f j
  have hp : 0 < R := by linarith
  have hh := hc L R hL hR M hM hQB (expandingSmoothHigh L R hp f) j
    (expandingSmoothHigh_low_zero L R (by linarith) hp f)
  have he : f = expandingSmoothLow L R hp f + expandingSmoothHigh L R hp f := by
    change f = expandingSmoothLow L R hp f + (f - expandingSmoothLow L R hp f)
    abel
  have hmap := congrArg
    (expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j) he
  rw [map_add] at hmap
  rw [hmap, add_sub_cancel_left]
  exact hh.trans (mul_le_mul_of_nonneg_left (expandingSmoothHigh_norm_le L R hp f)
    (div_nonneg hC (by linarith)))

end DefocusingNLS

end OAI

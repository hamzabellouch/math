import OAI.Analysis.LipschitzHilbert.Phase.InterpolationFamily

namespace OAI

/-!
# Finite bilinear interpolation with constant one

This is the finite simple-function step of §7. The analytic family is
constructed explicitly, and Hadamard's theorem proves the interpolated
pairing estimate from its two endpoint estimates.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePairing (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, K i j * a i * b j

theorem norm_finitePairing_le (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (w : κ → ℝ) (hK : ∀ i j, ‖K i j‖ ≤ w j) :
    ‖finitePairing K a b‖ ≤ (∑ i, ‖a i‖) * (∑ j, w j * ‖b j‖) := by
  unfold finitePairing
  calc
    _ ≤ ∑ i, ∑ j, ‖K i j * a i * b j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖a i‖ * (w j * ‖b j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK i j) (norm_nonneg (a i))) (norm_nonneg (b j))]
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

def pairingFamily (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) (z : ℂ) : ℂ :=
  finitePairing K (coefficientFamily a r 1 r₄ z) (coefficientFamily b s 1 (4 / 3) z)

theorem differentiable_pairingFamily (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) : Differentiable ℂ (pairingFamily K a b r s r₄) := by
  unfold pairingFamily finitePairing coefficientFamily
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.fun_sum
  intro j _
  exact ((differentiable_const (K i j)).mul
    (differentiable_magnitudeFamily (a i) _ _)).mul
    (differentiable_magnitudeFamily (b j) _ _)

theorem pairingFamily_bddAbove (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) : BddAbove ((norm ∘ pairingFamily K a b r s r₄) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i, ∑ j, ‖K i j‖ *
    (‖a i‖ ^ min (r / 1) (r / r₄) + ‖a i‖ ^ max (r / 1) (r / r₄)) *
    (‖b j‖ ^ min (s / 1) (s / (4 / 3)) + ‖b j‖ ^ max (s / 1) (s / (4 / 3))), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  change 0 ≤ z.re ∧ z.re ≤ 1 at hz
  simp only [Function.comp_apply]
  unfold pairingFamily finitePairing
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul, coefficientFamily]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (norm_magnitudeFamily_le (a i) _ _ hz.1 hz.2)
      (norm_nonneg _)
  · exact norm_magnitudeFamily_le (b j) _ _ hz.1 hz.2
  · exact norm_nonneg _
  · positivity

/-- The exact normalized finite pairing estimate supplied by the
coefficient and simple-test-function interpolation families. -/
theorem finite_pairing_interpolation (K : ι → κ → ℂ) (w : κ → ℝ)
    (hK : ∀ i j, ‖K i j‖ ≤ w j)
    {r s r₄ t : ℝ} (hr : 0 < r) (hs : 0 < s) (hr₄ : 0 < r₄)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / r₄) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (hfour : ∀ (a : ι → ℂ) (b : κ → ℂ),
      (∑ i, ‖a i‖ ^ r₄) = 1 → (∑ j, w j * ‖b j‖ ^ (4 / 3 : ℝ)) = 1 →
      ‖finitePairing K a b‖ ≤ 1)
    (a : ι → ℂ) (b : κ → ℂ)
    (ha : (∑ i, ‖a i‖ ^ r) = 1) (hb : (∑ j, w j * ‖b j‖ ^ s) = 1) :
    ‖finitePairing K a b‖ ≤ 1 := by
  let F := pairingFamily K a b r s r₄
  have hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ 1 := by
    intro z hz
    have hz' : z.re = 0 := hz
    have hA : (∑ i, ‖coefficientFamily a r 1 r₄ z i‖) = 1 := by
      simpa only [Real.rpow_one, ha] using
        (coefficientFamily_left_power_sum a hr (by norm_num : (0 : ℝ) < 1) hz')
    have hB : (∑ j, w j * ‖coefficientFamily b s 1 (4 / 3) z j‖) = 1 := by
      simpa only [Real.rpow_one, hb] using
        (weighted_magnitudeFamily_left_power_sum w b hs (by norm_num : (0 : ℝ) < 1) hz')
    exact (norm_finitePairing_le K _ _ w hK).trans_eq (by rw [hA, hB, mul_one])
  have hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ 1 := by
    intro z hz
    have hz' : z.re = 1 := hz
    apply hfour
    · exact (coefficientFamily_right_power_sum a hr hr₄ hz').trans ha
    · exact (weighted_magnitudeFamily_right_power_sum w b hs (by norm_num) hz').trans hb
  have hz : (t : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := ⟨ht0, ht1⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    F hz (differentiable_pairingFamily K a b r s r₄).diffContOnCl
    (pairingFamily_bddAbove K a b r s r₄) hleft hright
  have htarget : F (t : ℂ) = finitePairing K a b := by
    dsimp [F, pairingFamily]
    rw [coefficientFamily_at_real a r 1 r₄ t hrdef,
      coefficientFamily_at_real b s 1 (4 / 3) t hsdef]
  simpa only [htarget, Real.one_rpow, one_mul] using h

theorem finitePairing_div_right (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ) (c : ℂ) :
    finitePairing K a (fun j => b j / c) = finitePairing K a b / c := by
  unfold finitePairing
  simp only [← mul_div_assoc, ← Finset.sum_div]

/-- Scaling removes the unit-norm restriction on the simple test.
The coefficient sequence remains normalized. -/
theorem finite_pairing_interpolation_test (K : ι → κ → ℂ) (w : κ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hK : ∀ i j, ‖K i j‖ ≤ w j)
    {r s r₄ t : ℝ} (hr : 0 < r) (hs : 0 < s) (hr₄ : 0 < r₄)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / r₄) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (hfour : ∀ (a : ι → ℂ) (b : κ → ℂ),
      (∑ i, ‖a i‖ ^ r₄) = 1 → (∑ j, w j * ‖b j‖ ^ (4 / 3 : ℝ)) = 1 →
      ‖finitePairing K a b‖ ≤ 1)
    (a : ι → ℂ) (b : κ → ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖finitePairing K a b‖ ≤ (∑ j, w j * ‖b j‖ ^ s) ^ (1 / s) := by
  let S := ∑ j, w j * ‖b j‖ ^ s
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hzero : S = 0
  · have hterm (j : κ) : w j * ‖b j‖ ^ s = 0 := by
      have hle : w j * ‖b j‖ ^ s ≤ S :=
        Finset.single_le_sum (fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (norm_nonneg _) _))
          (Finset.mem_univ j)
      exact le_antisymm (hle.trans hzero.le) (mul_nonneg (hw j) (Real.rpow_nonneg (norm_nonneg _) _))
    have hlinear (j : κ) : w j * ‖b j‖ = 0 := by
      by_cases hb : b j = 0
      · simp [hb]
      · have hpos : 0 < ‖b j‖ ^ s := Real.rpow_pos_of_pos (norm_pos_iff.mpr hb) _
        have hwzero : w j = 0 := (mul_eq_zero.mp (hterm j)).resolve_right hpos.ne'
        simp [hwzero]
    have hle := norm_finitePairing_le K a b w hK
    simp only [hlinear, Finset.sum_const_zero, mul_zero] at hle
    change ‖finitePairing K a b‖ ≤ S ^ (1 / s)
    rw [hzero, Real.zero_rpow (one_div_ne_zero hs.ne')]
    exact hle
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    let B := S ^ (1 / s)
    have hB : 0 < B := Real.rpow_pos_of_pos hSpos _
    have hBpow : B ^ s = S := by
      dsimp [B]
      rw [← Real.rpow_mul hS]
      have he : (1 / s) * s = 1 := by field_simp
      rw [he, Real.rpow_one]
    let b' := fun j => b j / (B : ℂ)
    have hb' : (∑ j, w j * ‖b' j‖ ^ s) = 1 := by
      dsimp [b']
      simp_rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB.le,
        Real.div_rpow (norm_nonneg _) hB.le, ← mul_div_assoc]
      rw [← Finset.sum_div, hBpow, div_self hzero]
    have h := finite_pairing_interpolation K w hK hr hs hr₄ ht0 ht1 hrdef hsdef hfour a b' ha hb'
    dsimp [b'] at h
    rw [finitePairing_div_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB.le] at h
    exact (div_le_one hB).mp h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI

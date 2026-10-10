import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CenteredShellMoments

namespace OAI

/-!
Subtracting the cutoff mean reduces an uncentered height test to the normalized energy
estimate. Centered moment and tail bounds determine the resulting quantitative coefficient.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def uncenteredEnergyCoefficient (p : ℕ) (C B M c H R β W A : ℝ) (K L : ℝ≥0) : ℝ :=
  normalizedEnergyCoefficient p C (2 * (1 + M / c) * M) H R A
    (heightTailLinearCoefficient (p + 1) C (2 * (1 + M / c) * B) R β K
      (W + Real.sqrt (M / c))) L

theorem uncentered_inner_energy_bound {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, u x - u y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (r H R : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hHR : 2 * H ≤ R) (hrR : r ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hχone : ∀ x ∈ ball a r, χ x = 1)
    (M c δ β W A : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ1 : 1 ≤ β) (hβ2 : β < 2) (hW : |u a| ≤ W) (hA : 0 ≤ A)
    (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2)
    (hsmall : |rieszScalarPairing (p + 1) μ a R e
      (fun x => χ x ^ 2 * (u x - cutoffMean (μ.restrict (ball a R)) u χ))| ≤ A * δ ^ 3) :
    0 ≤ uncenteredEnergyCoefficient p C B M c H R β W A K L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
        ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ≤
        uncenteredEnergyCoefficient p C B M c H R β W A K L := by
  let ν := μ.restrict (ball a R)
  let b := cutoffMean ν u χ
  let w := fun x => u x - b
  let D := M / c
  let F := 2 * (1 + D)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hD : 0 ≤ D := div_nonneg hM hc.le
  have hF : 1 ≤ F := by dsimp [F]; linarith
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hCB' : C * 2 ^ (p + 1) ≤ F * B := hCB.trans
    (by simpa only [one_mul] using! mul_le_mul_of_nonneg_right hF hB)
  have hM' : M ≤ F * M := by simpa only [one_mul] using! mul_le_mul_of_nonneg_right hF hM
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hRpos
  have huL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hRpos
  have hνmass : ν.real univ ≤ M :=
    (ball_restriction_mass_bound (p + 1) C μ hg a R hRpos).trans hmass
  have hb : b ^ 2 ≤ D * δ ^ 2 := cutoffMean_sq_le_amplitude ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ hc hcutmass hsecond
  have hbabs : |b| ≤ Real.sqrt D := cutoffMean_abs_le_uniform ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ hc hM hδ.le hδ1 hcutmass hsecond
  have hw : LipschitzWith K w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [w, Real.dist_eq, centered_coordinate_difference] using! hu.dist_le_mul x y
  have hwcoord : ∀ x y, w x - w y = inner ℝ e (x - y) := by
    intro x y
    dsimp only [w]
    rw [centered_coordinate_difference, hcoord]
  have hwW : |w a| ≤ W + Real.sqrt D := by
    calc
      _ ≤ |u a| + |b| := by simpa only [w, sub_zero, zero_sub, abs_neg] using! abs_sub_le (u a) 0 b
      _ ≤ _ := add_le_add hW hbabs
  have hwsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ (F * M) * δ ^ 2 :=
    centered_moment_from_scale ν u huL2 M D δ δ b hM hD hνmass hsecond hb le_rfl
  have hwshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      ((F * B) * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2 := by
    intro k hk
    exact centered_shell_second_moment (p + 1) C B μ hg hCB u K hu a R hR k
      δ β D b hδ.le hβ1 hD hb (hshell k hk)
  have hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0 :=
    cutoffMean_integral_zero ν u χ hu.continuous.measurable hχ.continuous.measurable
      huL2 hχbound (ne_of_gt (hc.trans_le hcutmass))
  have hwsmall : |rieszScalarPairing (p + 1) μ a R e (fun x => χ x ^ 2 * w x)| ≤ A * δ ^ 2 := by
    apply hsmall.trans
    calc
      A * δ ^ 3 = (A * δ ^ 2) * δ := by ring
      _ ≤ (A * δ ^ 2) * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = _ := mul_one _
  obtain ⟨hconstant, hE, hbound⟩ := normalized_energy_from_vector_pairing p C (F * B) μ hg hCB'
    e w χ K L hw hχ hwcoord hχbound a H R hH hRpos hHR hχsupport
    (F * M) δ β (W + Real.sqrt D) A (mul_nonneg (by linarith) hM) hδ (by linarith) hβ2
    hwW hA N hlast (hmass.trans hM') hwsecond hwshell hzero hwsmall
  obtain ⟨hInner, hInnerBound⟩ := inner_fractional_energy_le_cutoff (p + 1) μ
    (ball a r) (ball a R) measurableSet_ball (ball_subset_ball hrR) u χ b δ hχone hE
  exact ⟨hconstant, hInner, hInnerBound.trans hbound⟩

end

end RieszRectifiability

end OAI

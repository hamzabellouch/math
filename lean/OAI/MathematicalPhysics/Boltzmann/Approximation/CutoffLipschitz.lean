import OAI.MathematicalPhysics.Boltzmann.Branching.GainSmoothingError

namespace OAI

/-! # Local weighted Lipschitz bounds for the finite-cutoff equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CutoffLipschitz

theorem gain_difference (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity, |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| ≤
      (D * (A + B) * HotApplication.realBound q) * H q v := by
  have hforward := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hA hB hD
    hfm hgm hf hg hfB hgB (fun w => (le_abs_self _).trans (hfg w)) b
  have hbackward := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hB hA hD
    hgm hfm hg hf hgB hfB (fun w => (le_abs_self _).trans (by simpa only [abs_sub_comm] using hfg w)) b
  filter_upwards [hforward, hbackward] with v hv hv'
  rw [add_comm B A] at hv'
  exact abs_le.mpr ⟨by linarith, hv⟩

def frequencyConstant (q b : ℝ) : ℝ := 2 * Real.pi * b * ∫ w, H q w

theorem frequencyConstant_nonneg {b : ℝ} (hb : 0 ≤ b) (q : ℝ) : 0 ≤ frequencyConstant q b := by
  unfold frequencyConstant
  have hi : 0 ≤ ∫ w, H q w := integral_nonneg (H_nonneg q)
  positivity

theorem integrable_dominated {q A : ℝ} (hq : q < 2) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ A * H q w) : Integrable f := by
  apply ((integrable_H hq).const_mul A).mono' hfm.aestronglyMeasurable
  filter_upwards [] with w
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf w)] using hfB w

theorem frequency_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.frequency b f v := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤ A * frequencyConstant q b := by
  have hi := integrable_dominated hq hfm hf hfB
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w| :=
      (le_abs_self _).trans (CollisionCutoff.abs_frequency_le hb hi v)
    _ ≤ 2 * Real.pi * b * ∫ w, A * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hi.abs ((integrable_H hq).const_mul A)
        (fun w => by simpa only [abs_of_nonneg (hf w)] using hfB w)
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) :
    |CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v| ≤ D * frequencyConstant q b := by
  have hfi := integrable_dominated hq hfm hf hfB
  have hgi := integrable_dominated hq hgm hg hgB
  have he : CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v =
      CollisionCutoff.frequency b (fun w => f w - g w) v := by
    unfold CollisionCutoff.frequency
    rw [← mul_sub, ← integral_sub (CollisionCutoff.integrable_frequency hb hfi v)
      (CollisionCutoff.integrable_frequency hb hgi v)]
    congr 2
    funext w
    ring
  rw [he]
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w - g w| :=
      CollisionCutoff.abs_frequency_le hb (hfi.sub hgi) v
    _ ≤ 2 * Real.pi * b * ∫ w, D * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (hfi.sub hgi).abs ((integrable_H hq).const_mul D) hfg
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

theorem loss_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) :
    |f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v| ≤
      (D * (A + B) * frequencyConstant q b) * H q v := by
  have hνf := frequency_nonneg hf b v
  have hνB := frequency_bound hq hb hfm hf hfB v
  have hνD := frequency_difference hq hb hfm hgm hf hg hfB hgB hfg v
  calc
    _ = |(f v - g v) * CollisionCutoff.frequency b f v +
        g v * (CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v)| := by congr 1; ring
    _ ≤ |f v - g v| * CollisionCutoff.frequency b f v +
        g v * |CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v| := by
      simpa only [abs_mul, abs_of_nonneg hνf, abs_of_nonneg (hg v)] using abs_add_le
        ((f v - g v) * CollisionCutoff.frequency b f v)
        (g v * (CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v))
    _ ≤ (D * H q v) * (A * frequencyConstant q b) + (B * H q v) * (D * frequencyConstant q b) :=
      add_le_add (mul_le_mul (hfg v) hνB hνf (mul_nonneg hD (H_nonneg q v)))
        (mul_le_mul (hgB v) hνD (abs_nonneg _) (mul_nonneg hB (H_nonneg q v)))
    _ = _ := by ring

def collision (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  CollisionCutoff.gain b f v - f v * CollisionCutoff.frequency b f v

/-- The local difference constant for the actual cutoff collision field. -/
theorem collision_difference (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) :
    ∀ᵐ v : Velocity, |collision b f v - collision b g v| ≤
      (D * (A + B) * (HotApplication.realBound q + frequencyConstant q b)) * H q v := by
  filter_upwards [gain_difference hcarleman hq₁ hq₂ hA hB hD hfm hgm hf hg hfB hgB hfg b]
    with v hv
  have hl := loss_difference hq₂ hb hB hD hfm hgm hf hg hfB hgB hfg v
  calc
    _ = |(CollisionCutoff.gain b f v - CollisionCutoff.gain b g v) -
        (f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v)| := by
      unfold collision
      congr 1
      ring
    _ ≤ |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| +
        |f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v| := abs_sub _ _
    _ ≤ _ := by nlinarith only [hv, hl]

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI

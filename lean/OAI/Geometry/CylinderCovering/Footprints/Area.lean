import OAI.Geometry.CylinderCovering.Footprints.FootprintsDefinitions

namespace OAI

open Set MeasureTheory

namespace RadialFootprints

theorem closed_region_volume (f g : ℝ → ℝ) (s : Set ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

theorem symmetric_strip_volume {l r : ℝ} (hlr : l ≤ r)
    (f w : ℝ → ℝ) (hf : Continuous f) (hw : Continuous w)
    (hw0 : ∀ x ∈ Icc l r, 0 ≤ w x) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc l r ∧ |p.2 - f p.1| ≤ w p.1} =
      ENNReal.ofReal (∫ x in l..r, 2 * w x) := by
  have heq : {p : ℝ × ℝ | p.1 ∈ Icc l r ∧ |p.2 - f p.1| ≤ w p.1} =
      {p : ℝ × ℝ | p.1 ∈ Icc l r ∧
        p.2 ∈ Icc (f p.1 - w p.1) (f p.1 + w p.1)} := by
    ext p
    simp only [mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨hp, hleft, hright⟩ <;>
      exact ⟨hp, by linarith, by linarith⟩
  rw [heq, closed_region_volume (fun x => f x - w x) (fun x => f x + w x)
    (Icc l r) (hf.sub hw).measurable (hf.add hw).measurable measurableSet_Icc]
  change (volume.prod volume) _ = _
  rw [volume_regionBetween_eq_integral
    (f := fun x => f x - w x) (g := fun x => f x + w x)
    (s := Icc l r) (μ := volume) (hf.sub hw).integrableOn_Icc
    (hf.add hw).integrableOn_Icc measurableSet_Icc
    (by intro x hx; have := hw0 x hx; linarith)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  ring

theorem integral_linear (l r p q : ℝ) :
    (∫ x in l..r, p * x + q) = p * ((r ^ 2 - l ^ 2) / 2) + (r - l) * q := by
  rw [intervalIntegral.integral_add (f := fun x => p * x) (g := fun _ => q)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  rfl

theorem integral_affine_width (A B M d : ℝ) :
    (∫ x in (-A * d)..(M + A * d), d * x + 2 * B * d ^ 2) =
      d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 + 4 * A * B * d ^ 3 := by
  rw [integral_linear]
  ring

theorem integral_absolute_width {A M d : ℝ} (B : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    (∫ x in (-A * d)..(M + A * d), d * |x| + 2 * B * d ^ 2) =
      d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 +
        (A ^ 2 + 4 * A * B) * d ^ 3 := by
  have hl : -A * d ≤ 0 := by nlinarith [mul_nonneg hA hd]
  have hr : 0 ≤ M + A * d := add_nonneg hM (mul_nonneg hA hd)
  have hc : Continuous (fun x : ℝ => d * |x| + 2 * B * d ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-A * d) 0) (hc.intervalIntegrable 0 (M + A * d))]
  have hleft : (∫ x in (-A * d)..0, d * |x| + 2 * B * d ^ 2) =
      ∫ x in (-A * d)..0, (-d) * x + 2 * B * d ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hl] at hx
    dsimp
    rw [abs_of_nonpos hx.2]
    ring
  have hright : (∫ x in (0 : ℝ)..(M + A * d), d * |x| + 2 * B * d ^ 2) =
      ∫ x in (0 : ℝ)..(M + A * d), d * x + 2 * B * d ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr] at hx
    dsimp
    rw [abs_of_nonneg hx.1]
  rw [hleft, hright]
  rw [integral_linear, integral_linear]
  ring

theorem absoluteFootprint_volume {A B M d : ℝ} (m : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    volume (absoluteFootprint A B M d m) = ENNReal.ofReal
      (d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 +
        (A ^ 2 + 4 * A * B) * d ^ 3) := by
  have hlr : -A * d ≤ M + A * d := by nlinarith [mul_nonneg hA hd]
  rw [absoluteFootprint, symmetric_strip_volume hlr
    (fun x => m * x) (fun x => d / 2 * |x| + B * d ^ 2)
    (by fun_prop) (by fun_prop) (by intro x hx; positivity)]
  congr 1
  calc
    (∫ x in (-A * d)..(M + A * d), 2 * (d / 2 * |x| + B * d ^ 2)) =
        ∫ x in (-A * d)..(M + A * d), d * |x| + 2 * B * d ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp
      ring
    _ = _ := integral_absolute_width B hA hM hd

theorem absoluteFootprint_area {A B M d : ℝ} (m : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    volume.real (absoluteFootprint A B M d m) =
      d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 +
        (A ^ 2 + 4 * A * B) * d ^ 3 := by
  rw [measureReal_def, absoluteFootprint_volume m hA hB hM hd,
    ENNReal.toReal_ofReal (by positivity)]

theorem affineFootprint_volume {A B M d : ℝ} (m : ℝ)
    (hA : 0 ≤ A) (hB : A / 2 ≤ B) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    volume (affineFootprint A B M d m) = ENNReal.ofReal
      (d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 + 4 * A * B * d ^ 3) := by
  have hlr : -A * d ≤ M + A * d := by nlinarith [mul_nonneg hA hd]
  have hw0 : ∀ x ∈ Icc (-A * d) (M + A * d), 0 ≤ d / 2 * x + B * d ^ 2 := by
    intro x hx
    have h1 := mul_nonneg hd (show 0 ≤ x + A * d by linarith [hx.1])
    have h2 := mul_nonneg (show 0 ≤ B - A / 2 by linarith) (sq_nonneg d)
    nlinarith
  rw [affineFootprint, symmetric_strip_volume hlr
    (fun x => m * x) (fun x => d / 2 * x + B * d ^ 2)
    (by fun_prop) (by fun_prop) hw0]
  congr 1
  calc
    (∫ x in (-A * d)..(M + A * d), 2 * (d / 2 * x + B * d ^ 2)) =
        ∫ x in (-A * d)..(M + A * d), d * x + 2 * B * d ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp
      ring
    _ = _ := integral_affine_width A B M d

theorem affineFootprint_area {A B M d : ℝ} (m : ℝ)
    (hA : 0 ≤ A) (hB : A / 2 ≤ B) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    volume.real (affineFootprint A B M d m) =
      d * M ^ 2 / 2 + (A + 2 * B) * M * d ^ 2 + 4 * A * B * d ^ 3 := by
  have hB0 : 0 ≤ B := le_trans (by positivity : 0 ≤ A / 2) hB
  rw [measureReal_def, affineFootprint_volume m hA hB hM hd,
    ENNReal.toReal_ofReal (by positivity)]

theorem halfheightFootprint_volume {ρ e M : ℝ} (m : ℝ)
    (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hM : 0 ≤ M) :
    volume (halfheightFootprint ρ e M m) =
      ENNReal.ofReal (ρ * (M ^ 2 + 6 * e * M + 8 * e ^ 2)) := by
  have hlr : -e ≤ M + e := by linarith
  rw [halfheightFootprint, symmetric_strip_volume hlr
    (fun x => m * x) (fun x => ρ * (x + 2 * e))
    (by fun_prop) (by fun_prop)
    (by intro x hx; exact mul_nonneg hρ (by linarith [hx.1]))]
  congr 1
  calc
    (∫ x in (-e)..(M + e), 2 * (ρ * (x + 2 * e))) =
        ∫ x in (-e)..(M + e), (2 * ρ) * x + 4 * ρ * e := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp
      ring
    _ = _ := by rw [integral_linear]; ring

theorem halfheightFootprint_area {ρ e M : ℝ} (m : ℝ)
    (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hM : 0 ≤ M) :
    volume.real (halfheightFootprint ρ e M m) =
      ρ * (M ^ 2 + 6 * e * M + 8 * e ^ 2) := by
  rw [measureReal_def, halfheightFootprint_volume m hρ he hM,
    ENNReal.toReal_ofReal (by positivity)]

end RadialFootprints

end OAI

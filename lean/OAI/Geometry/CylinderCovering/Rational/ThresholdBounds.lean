import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions
import OAI.Geometry.CylinderCovering.Convexity.ThresholdRemainder

namespace OAI

noncomputable section

namespace SlopeRational.Threshold
open scoped ContDiff
open Set

private theorem coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

private theorem norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0| + |z 1| := by
  have h : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs]
  nlinarith [sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0), abs_nonneg (z 1)]

private theorem field_smooth {d : ℝ} {z : Plane} (hz : 0 < radius (z 1) + d) :
    ContDiffAt ℝ ∞ (field d) z := by
  apply (contDiffAt_piLp 2).2
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : Plane => a d (w 0) (w 1)) z
    unfold a radius
    dsimp [radius] at hz
    fun_prop (disch := positivity)
  · change ContDiffAt ℝ ∞ (fun w : Plane => b d (w 0) (w 1)) z
    unfold b radius
    dsimp [radius] at hz
    fun_prop (disch := positivity)

private theorem divider_a (d y : ℝ) : a d y 0 = -ceilingCoefficient d y := by
  unfold a radius ceilingCoefficient ceilingConstant ceilingQuadratic
  ring

private theorem divider_b {d : ℝ} (hd : 0 < d) (y : ℝ) : b d y 0 = alpha d * y := by
  have h1 : 1 + 2 * d ≠ 0 := by positivity
  have h2 : (1 / 2 : ℝ) + d ≠ 0 := by positivity
  unfold b radius alpha
  field_simp
  ring

theorem region_estimates {d : ℝ} (hd : 0 < d) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ Y T y : ℝ,
      |Y| ≤ 1 → -1 ≤ T → T ≤ 1 / 2 + d / 2 → |y| ≤ 1 →
      |a d Y T| ≤ L ∧ |ceilingPolynomial d y| ≤ L ∧
      |a d Y T + ceilingCoefficient d y| ≤ L * (|Y - y| + |T|) ∧
      |b d Y T - alpha d * Y| ≤ L * |T| ∧
      |ceilingPolynomial d Y - ceilingPolynomial d y| ≤ L * |Y - y| := by
  let S : Set Plane := (EuclideanSpace.proj 0) ⁻¹' Icc (-1 : ℝ) 1 ∩
    (EuclideanSpace.proj 1) ⁻¹' Icc (-1 : ℝ) (1 / 2 + d / 2)
  have hSc : IsClosed S := (isClosed_Icc.preimage (by fun_prop)).inter
    (isClosed_Icc.preimage (by fun_prop))
  have hS : IsCompact S := (isCompact_closedBall (0 : Plane) (3 + d)).of_isClosed_subset hSc (by
    intro z hz
    change z 0 ∈ Icc (-1 : ℝ) 1 ∧ z 1 ∈ Icc (-1 : ℝ) (1 / 2 + d / 2) at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h0 : |z 0| ≤ 1 := abs_le.mpr hz.1
    have h1 : |z 1| ≤ 2 + d := abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact (norm_le_sum z).trans (by linarith))
  have hconv : Convex ℝ S :=
    ((convex_Icc (-1 : ℝ) 1).linear_preimage (EuclideanSpace.proj 0).toLinearMap).inter
      ((convex_Icc (-1 : ℝ) (1 / 2 + d / 2)).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hsmooth : ∀ z ∈ S, ContDiffAt ℝ ∞ (field d) z := by
    intro z hz
    apply field_smooth
    have hz1 : z 1 ≤ 1 / 2 + d / 2 := hz.2.2
    dsimp [radius]
    linarith
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (hsmooth z hz).continuousAt.continuousWithinAt)
  obtain ⟨C₁, hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((hsmooth z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  have hpoly : ContDiff ℝ ∞ (ceilingPolynomial d) := by
    unfold ceilingPolynomial ceilingCoefficient
    fun_prop
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fderiv ℝ (ceilingPolynomial d))
    (fun _ _ => (hpoly.contDiffAt.continuousAt_fderiv (by norm_num)).continuousWithinAt)
  obtain ⟨C₃, hC₃⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hpoly.continuous.continuousOn
  let L := max 1 (max C₀ (max C₁ (max C₂ C₃)))
  have hL : 1 ≤ L := le_max_left _ _
  have hL₀ : C₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hL₁ : C₁ ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hL₂ : C₂ ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hL₃ : C₃ ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hL0 : 0 ≤ L := by linarith
  have hlip : ∀ z ∈ S, ∀ w ∈ S, ‖field d z - field d w‖ ≤ L * ‖z - w‖ := by
    intro z hz w hw
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => (hsmooth q hq).differentiableAt (by norm_num))
      (fun q hq => (hC₁ q hq).trans hL₁) hconv hw hz
  have hplip : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ Y ∈ Icc (-1 : ℝ) 1,
      |ceilingPolynomial d Y - ceilingPolynomial d y| ≤ L * |Y - y| := by
    intro y hy Y hY
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := ceilingPolynomial d) (fun _ _ => hpoly.differentiable (by norm_num) _)
      (fun q hq => (hC₂ q hq).trans hL₂) (convex_Icc _ _) hy hY
  refine ⟨L, hL, ?_⟩
  intro Y T y hY hT0 hT1 hy
  have hz : vec2 Y T ∈ S := by exact ⟨abs_le.mp hY, hT0, hT1⟩
  have hw : vec2 Y 0 ∈ S := by
    refine ⟨abs_le.mp hY, ?_, ?_⟩ <;> dsimp [vec2] <;> linarith
  have hwy : vec2 y 0 ∈ S := by
    refine ⟨abs_le.mp hy, ?_, ?_⟩ <;> dsimp [vec2] <;> linarith
  refine ⟨?_, ?_, ?_, ?_, hplip y (abs_le.mp hy) Y (abs_le.mp hY)⟩
  · simpa [field, vec2] using (coordinate_le (field d (vec2 Y T)) 0).trans ((hC₀ _ hz).trans hL₀)
  · simpa only [Real.norm_eq_abs] using (hC₃ y (abs_le.mp hy)).trans hL₃
  · have hh := (coordinate_le (field d (vec2 Y T) - field d (vec2 y 0)) 0).trans
      (hlip _ hz _ hwy)
    have hn := norm_le_sum (vec2 Y T - vec2 y 0)
    have hn' : ‖vec2 Y T - vec2 y 0‖ ≤ |Y - y| + |T| := by
      simpa [vec2] using hn
    have hh' : |a d Y T - a d y 0| ≤ L * ‖vec2 Y T - vec2 y 0‖ := by
      simpa [field, vec2] using hh
    rw [divider_a, sub_neg_eq_add] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_left hn' hL0)
  · have hh := (coordinate_le (field d (vec2 Y T) - field d (vec2 Y 0)) 1).trans
      (hlip _ hz _ hw)
    have hn : ‖vec2 Y T - vec2 Y 0‖ ≤ |T| := by
      simpa [vec2] using norm_le_sum (vec2 Y T - vec2 Y 0)
    have hh' : |b d Y T - b d Y 0| ≤ L * ‖vec2 Y T - vec2 Y 0‖ := by
      simpa [field, vec2] using hh
    rw [divider_b hd] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_left hn hL0)

theorem threshold_remainder {d : ℝ} (hd : 0 < d) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ e x y Y T : ℝ,
      0 ≤ e → 4 * e * L ≤ 1 → |x| ≤ 1 → |y| ≤ 1 →
      |Y| ≤ 1 → -1 ≤ T → T ≤ 1 / 2 + d / 2 →
      y = Y + e * x * a d Y T →
      T + e * x * b d Y T = e * alpha d * x * y +
        e ^ 2 * (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y) →
      |T| ≤ 3 * L * e ^ 2 ∧
        |T + e ^ 2 * ceilingPolynomial d Y| ≤ 8 * L ^ 2 * e ^ 3 := by
  obtain ⟨L, hL, hreg⟩ := region_estimates hd
  refine ⟨L, hL, ?_⟩
  intro e x y Y T he hsmall hx hy hY hT0 hT1 hyeq hteq
  obtain ⟨ha, hP, haLip, hbLip, hPLip⟩ := hreg Y T y hY hT0 hT1 hy
  have hα : |alpha d| ≤ 1 := by
    unfold alpha
    rw [abs_of_pos (by positivity : 0 < 1 / (1 + 2 * d))]
    exact (div_le_one (by positivity : 0 < 1 + 2 * d)).2 (by linarith)
  exact CylinderCovering.ThresholdRemainder.inverse_threshold_remainder
    he hL hsmall hx hα ha hP haLip hbLip hPLip hyeq hteq

end SlopeRational.Threshold

end

end OAI

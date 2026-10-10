import OAI.Analysis.StrictMeans.StrictTransport

namespace OAI

section
open Set Filter Metric Complex
open scoped Topology

namespace StrictInverseFirstPower

noncomputable section

theorem disk_decay_zero_at_zero {g : ℂ → ℂ} {C : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hbound : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ C * (1 - ‖w‖ ^ 2)) :
    g 0 = 0 := by
  have h_circle (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      ‖g 0‖ ≤ C * (1 - r ^ 2) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.diffContOnCl_ball (closedBall_subset_ball hr1))
    · intro w hw
      rw [frontier_ball _ hr.ne'] at hw
      have hw' : ‖w‖ = r := by simpa using hw
      simpa [hw'] using hbound w (by simpa [mem_ball, dist_zero_right, hw'] using hr1)
    · exact subset_closure (mem_ball_self hr)
  have ht : Tendsto (fun r : ℝ => C * (1 - r ^ 2)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => C * (1 - r ^ 2)) := by fun_prop
    simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hn : ‖g 0‖ ≤ 0 := ge_of_tendsto ht (by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with r hr1 hr
    exact h_circle r hr hr1)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem halfPlane_linear_decay_zero {g : ℂ → ℂ} {C : ℝ}
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖g z‖ ≤ C * z.im) : g I = 0 := by
  let h : ℂ → ℂ := fun w => (1 - w) ^ 2 * g (cayleyToHalfPlane w)
  have hh : DifferentiableOn ℂ h (ball 0 1) := by
    apply DifferentiableOn.mul
    · fun_prop
    · exact hg.comp cayley_differentiableOn (fun w hw => cayley_mem_halfPlane hw)
  have hb : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ C * (1 - ‖w‖ ^ 2) := by
    intro w hw
    calc
      ‖h w‖ = ‖1 - w‖ ^ 2 * ‖g (cayleyToHalfPlane w)‖ := by
        simp [h, norm_pow]
      _ ≤ ‖1 - w‖ ^ 2 * (C * (cayleyToHalfPlane w).im) :=
        mul_le_mul_of_nonneg_left (hbound _ (cayley_mem_halfPlane hw)) (sq_nonneg _)
      _ = C * (1 - ‖w‖ ^ 2) := by
        rw [← cayley_im_mul_norm_sq (one_sub_ne_zero_of_mem_disk hw)]
        ring
  have hz := disk_decay_zero_at_zero hh hb
  simpa [h, cayleyToHalfPlane] using hz
theorem norm_logarithmicDerivative (F : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    ‖logarithmicDerivative F z‖ = z.im * ‖deriv (deriv F) z / deriv F z‖ := by
  simp [logarithmicDerivative, abs_of_pos hz]

theorem jacobian_eq_zero_lower_bound {F : ℂ → ℂ} {z : ℂ}
    (h : jacobianExpression (3 / 4) F z = 0) :
    1 / 4 ≤ ‖logarithmicDerivative F z‖ := by
  have hq := Complex.re_le_norm (logarithmicDerivative F z)
  have hn := norm_nonneg (logarithmicDerivative F z)
  unfold jacobianExpression at h
  have he := (div_eq_zero_iff.mp h).resolve_right (by norm_num)
  norm_num at he
  by_contra hlt
  have hlt' : ‖logarithmicDerivative F z‖ < 1 / 4 := lt_of_not_ge hlt
  have hsq : ‖logarithmicDerivative F z‖ ^ 2 < (1 / 4 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hn (by norm_num)).mpr hlt'
  nlinarith

theorem no_identically_zero_jacobianExpression {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) :
    ¬ ∀ z : ℂ, 0 < z.im → jacobianExpression (3 / 4) F z = 0 := by
  intro hJ
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' := hF.deriv hopen
  have hF'' := hF'.deriv hopen
  let p : ℂ → ℂ := fun z => deriv (deriv F) z / deriv F z
  have hlow (z : ℂ) (hz : 0 < z.im) : 1 / 4 ≤ z.im * ‖p z‖ := by
    simpa only [norm_logarithmicDerivative F hz] using jacobian_eq_zero_lower_bound (hJ z hz)
  have hp (z : ℂ) (hz : 0 < z.im) : p z ≠ 0 := by
    intro h
    have := hlow z hz
    simp only [h, norm_zero, mul_zero] at this
    norm_num at this
  have hFne (z : ℂ) (hz : 0 < z.im) : deriv F z ≠ 0 := by
    intro he
    exact hp z hz (by simp [p, he])
  have hpd : DifferentiableOn ℂ p {z : ℂ | 0 < z.im} :=
    hF''.div hF' (fun z hz => hFne z hz)
  have hgd : DifferentiableOn ℂ (fun z => (p z)⁻¹) {z : ℂ | 0 < z.im} :=
    hpd.inv (fun z hz => hp z hz)
  have hgb (z : ℂ) (hz : 0 < z.im) : ‖(p z)⁻¹‖ ≤ 4 * z.im := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (hp z hz))]
    nlinarith [hlow z hz]
  have hgz := halfPlane_linear_decay_zero hgd hgb
  exact inv_ne_zero (hp I (by simp)) hgz

end

end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_jacobianExpression_fixed (k : ℝ) (z : UpperHalfPlane) :
    Continuous (fun f : DiskFamily => jacobianExpression k (halfPlaneFunction f) z) := by
  let w : HalfPlaneSet := ⟨(z : ℂ), z.im_pos⟩
  have hp : Continuous (fun f : DiskFamily => (f, w)) := continuous_id.prodMk continuous_const
  have hc := (continuous_jacobianExpression k).comp hp
  exact hc

lemma ae_jacobian_zero_everywhere (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily))
    (hzero : ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression k (halfPlaneFunction f) I = 0)
    (z : UpperHalfPlane) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression k (halfPlaneFunction f) z = 0 := by
  let φ : C(DiskFamily, ℝ) := ⟨fun f => |jacobianExpression k (halfPlaneFunction f) I|,
    (continuous_jacobianExpression_fixed k UpperHalfPlane.I).abs⟩
  have hφ : ∫ f, φ f ∂(μ : Measure DiskFamily) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with f hf
    change |jacobianExpression k (halfPlaneFunction f) I| = 0
    rw [hf, abs_zero]
  have he := hlaw z φ
  simp only [hφ, mul_zero] at he
  have hfun (f : DiskFamily) : ‖halfPlaneQ f z‖ * φ (rebase f z) =
      ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction f) z| := by
    change ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction (rebase f z)) I| = _
    rw [jacobianExpression_rebase_I]
  have hc : Continuous (fun f : DiskFamily =>
      ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction f) z|) :=
    ((continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).norm).mul
      (continuous_jacobianExpression_fixed k z).abs
  have ha := (integral_eq_zero_iff_of_nonneg
    (fun f => mul_nonneg (norm_nonneg _) (abs_nonneg _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp
      (by simpa only [hfun] using he)
  filter_upwards [ha] with f hf
  exact abs_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left
    (norm_ne_zero_iff.mpr (halfPlaneQ_ne_zero f z)))

theorem affine_law_not_ae_zero_jacobian (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) :
    ¬ ∀ᵐ f ∂(μ : Measure DiskFamily),
      jacobianExpression (3 / 4) (halfPlaneFunction f) I = 0 := by
  intro hzero
  obtain ⟨f, hf⟩ := (μ : Measure DiskFamily).nonempty_support (by
    intro h
    have hu := measure_univ (μ := (μ : Measure DiskFamily))
    simp [h] at hu)
  apply no_identically_zero_jacobianExpression (halfPlaneFunction_differentiableOn f)
  intro z hz
  exact (μ : Measure DiskFamily).support_subset_of_isClosed
    (isClosed_eq (continuous_jacobianExpression_fixed (3 / 4) ⟨z, hz⟩) continuous_const)
    (ae_jacobian_zero_everywhere μ β (3 / 4) hlaw hzero ⟨z, hz⟩) hf

end
end StrictInverseFirstPower

end

end OAI

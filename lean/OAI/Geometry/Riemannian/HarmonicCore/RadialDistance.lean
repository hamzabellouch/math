import OAI.Geometry.Riemannian.HarmonicCore.PolarBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma inner_symm (g : SmoothMetric3) (x v w : E3) : g.inner x v w = g.inner x w v := by
  unfold inner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(Matrix.isHermitian_iff_isSymm.mp (g.positive x).isHermitian).apply i j]
  ring



lemma inner_sub_left (g : SmoothMetric3) (x u v w : E3) :
    g.inner x (u-v) w = g.inner x u w - g.inner x v w := by
  simp [inner, sub_mul, mul_sub, Finset.sum_sub_distrib]



lemma inner_smul_left (g : SmoothMetric3) (x u v : E3) (c : ℝ) :
    g.inner x (c • u) v = c * g.inner x u v := by
  simp only [inner, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring



lemma inner_sub_right (g : SmoothMetric3) (x u v w : E3) :
    g.inner x u (v-w) = g.inner x u v - g.inner x u w := by
  rw [g.inner_symm x u (v-w), g.inner_sub_left]
  rw [g.inner_symm x v u, g.inner_symm x w u]



lemma inner_smul_right (g : SmoothMetric3) (x u v : E3) (c : ℝ) :
    g.inner x u (c • v) = c * g.inner x u v := by
  rw [g.inner_symm x u (c • v), g.inner_smul_left, g.inner_symm x v u]



lemma inner_radial (g : SmoothMetric3) (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp)
    (x v : E3) : g.inner x v x = Inner.inner ℝ x v := by
  rw [g.inner_eq_dotProduct, hr, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]



lemma radial_cauchy_sq (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp) (x v : E3) :
    (Inner.inner ℝ x v)^2 ≤ ‖x‖^2 * g.inner x v v := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hq := g.inner_nonneg x (v - ((Inner.inner ℝ x v)/‖x‖^2) • x)
  rw [g.inner_sub_left, g.inner_sub_right, g.inner_smul_right,
    g.inner_smul_left, g.inner_sub_right, g.inner_smul_right,
    g.inner_radial hr, g.inner_symm x x v, g.inner_radial hr,
    g.inner_radial hr, real_inner_self_eq_norm_sq] at hq
  have hq' := mul_nonneg hn.le hq
  field_simp at hq'
  nlinarith



lemma regularized_radius_deriv_bound (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp)
    {γ : ℝ → E3} (hγ : ContDiff ℝ 1 γ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun s ↦ Real.sqrt (‖γ s‖^2+ε))
      ((Inner.inner ℝ (γ t) (deriv γ t)) / Real.sqrt (‖γ t‖^2+ε)) t ∧
    |(Inner.inner ℝ (γ t) (deriv γ t)) / Real.sqrt (‖γ t‖^2+ε)| ≤
      Real.sqrt (g.inner (γ t) (deriv γ t) (deriv γ t)) := by
  have hg := (hγ.differentiable (by simp) t).hasDerivAt
  have hpos : 0 < ‖γ t‖^2+ε := by positivity
  have hd := ((hg.inner ℝ hg).add_const ε).sqrt (by simpa only [real_inner_self_eq_norm_sq] using hpos.ne')
  have hd' : HasDerivAt (fun s ↦ Real.sqrt (‖γ s‖^2+ε))
      ((Inner.inner ℝ (γ t) (deriv γ t)) / Real.sqrt (‖γ t‖^2+ε)) t := by
    convert hd using 1
    · ext s; rw [real_inner_self_eq_norm_sq]
    · rw [real_inner_self_eq_norm_sq, real_inner_comm (deriv γ t) (γ t)]
      ring
  refine ⟨hd', ?_⟩
  have hp := g.inner_nonneg (γ t) (deriv γ t)
  have hcs := g.radial_cauchy_sq hr (γ t) (deriv γ t)
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hpos)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hpos)).2
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hpos.le]
  nlinarith [mul_nonneg hε.le hp]



lemma radius_change_le_pathLength (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp)
    {γ : ℝ → E3} (hγ : ContDiff ℝ 1 γ) :
    |‖γ 1‖-‖γ 0‖| ≤ g.pathLength γ := by
  have hb (ε : ℝ) (hε : 0 < ε) :
      |Real.sqrt (‖γ 1‖^2+ε)-Real.sqrt (‖γ 0‖^2+ε)| ≤ g.pathLength γ := by
    let u : ℝ → ℝ := fun t ↦ Real.sqrt (‖γ t‖^2+ε)
    have hu : Differentiable ℝ u := fun t ↦
      (g.regularized_radius_deriv_bound hr hγ hε t).1.differentiableAt
    apply norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num : (0:ℝ) ≤ 1)
      hu.continuous.continuousOn hu.differentiableOn
      _ ((g.pathSpeed_continuous hγ).intervalIntegrable 0 1)
    filter_upwards [] with t ht
    rw [(g.regularized_radius_deriv_bound hr hγ hε t).1.deriv, Real.norm_eq_abs]
    exact (g.regularized_radius_deriv_bound hr hγ hε t).2
  have ht : Tendsto (fun ε : ℝ ↦
      |Real.sqrt (‖γ 1‖^2+ε)-Real.sqrt (‖γ 0‖^2+ε)|)
      (𝓝[>] 0) (𝓝 |‖γ 1‖-‖γ 0‖|) := by
    have he : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := ((((tendsto_const_nhds (x := ‖γ 1‖^2)).add he).sqrt).sub
      (((tendsto_const_nhds (x := ‖γ 0‖^2)).add he).sqrt)).abs
    simpa only [add_zero, Real.sqrt_sq (norm_nonneg _)] using
      (h : Tendsto (fun ε : ℝ ↦
        |Real.sqrt (‖γ 1‖^2+ε)-Real.sqrt (‖γ 0‖^2+ε)|)
        (𝓝[>] 0) (𝓝 |Real.sqrt (‖γ 1‖^2+0)-Real.sqrt (‖γ 0‖^2+0)|))
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hb ε hε



lemma radius_change_le_distance (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp) (x y : E3) :
    |‖y‖-‖x‖| ≤ g.distance x y := by
  apply le_csInf (g.paths_nonempty x y)
  rintro l ⟨γ, hγ, hx, hy, rfl⟩
  simpa only [hx, hy] using g.radius_change_le_pathLength hr hγ



lemma radial_straight_length (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp) (h0 : g.coeff 0 = 1)
    (x : E3) : g.pathLength (fun t : ℝ ↦ t • x) = ‖x‖ := by
  have hd (t : ℝ) : deriv (fun s : ℝ ↦ s • x) t = x := by
    simpa only [zero_add, sub_zero] using straight_deriv (0 : E3) x t
  have hi (t : ℝ) : g.inner (t • x) x x = ‖x‖^2 := by
    by_cases ht : t = 0
    · simp only [ht, zero_smul, g.inner_eq_dotProduct, h0, Matrix.one_mulVec,
        dotProduct_self_norm]
    · have h := g.inner_radial hr (t • x) x
      rw [g.inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
      exact mul_left_cancel₀ ht h
  unfold pathLength
  simp only [hd, hi, Real.sqrt_sq (norm_nonneg _)]
  simp



lemma distance_origin_eq_norm (g : SmoothMetric3)
    (hr : ∀ x : E3, g.coeff x *ᵥ x.ofLp = x.ofLp) (h0 : g.coeff 0 = 1)
    (x : E3) : g.distance 0 x = ‖x‖ := by
  apply le_antisymm
  · have hsm : ContDiff ℝ 1 (fun t : ℝ ↦ t • x) := contDiff_id.smul contDiff_const
    have h := g.distance_le_pathLength hsm
    simpa only [zero_smul, one_smul, g.radial_straight_length hr h0 x] using h
  · simpa only [norm_zero, sub_zero, abs_of_nonneg (norm_nonneg _)] using
      g.radius_change_le_distance hr 0 x

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI

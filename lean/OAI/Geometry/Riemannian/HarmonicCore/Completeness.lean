import OAI.Geometry.Riemannian.HarmonicCore.Model

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

lemma inner_eq_dotProduct (g : SmoothMetric3) (x v w : E3) :
    g.inner x v w = v.ofLp ⬝ᵥ (g.coeff x *ᵥ w.ofLp) := by
  simp only [inner, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



lemma inner_nonneg (g : SmoothMetric3) (x v : E3) : 0 ≤ g.inner x v v := by
  rw [inner_eq_dotProduct]
  simpa using (g.positive x).posSemidef.dotProduct_mulVec_nonneg v.ofLp



lemma inner_continuous {T : Type*} [TopologicalSpace T] (g : SmoothMetric3)
    {x v w : T → E3} (hx : Continuous x) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun t ↦ g.inner (x t) (v t) (w t)) := by
  unfold inner
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((g.smooth i j).continuous.comp hx).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hv)).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hw)



lemma pathSpeed_continuous (g : SmoothMetric3) {γ : ℝ → E3}
    (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun t ↦ Real.sqrt (g.inner (γ t) (deriv γ t) (deriv γ t))) :=
  (g.inner_continuous hγ.continuous (hγ.continuous_deriv le_rfl)
    (hγ.continuous_deriv le_rfl)).sqrt



lemma distance_le_pathLength (g : SmoothMetric3) {γ : ℝ → E3}
    (hγ : ContDiff ℝ 1 γ) : g.distance (γ 0) (γ 1) ≤ g.pathLength γ := by
  apply csInf_le
  · exact ⟨0, fun l hl ↦ by rcases hl with ⟨η, _, _, _, rfl⟩; exact g.pathLength_nonneg η⟩
  · exact ⟨γ, hγ, rfl, rfl, rfl⟩



lemma straight_smooth (x y : E3) : ContDiff ℝ 1 (fun t : ℝ ↦ x+t • (y-x)) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)



lemma straight_deriv (x y : E3) (t : ℝ) :
    deriv (fun t : ℝ ↦ x+t • (y-x)) t = y-x := by
  simpa using (((hasDerivAt_id t).smul_const (y-x)).const_add x).deriv



lemma paths_nonempty (g : SmoothMetric3) (x y : E3) :
    {l : ℝ | ∃ γ : ℝ → E3, ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧
      l = g.pathLength γ}.Nonempty := by
  refine ⟨_, fun t ↦ x+t • (y-x), straight_smooth x y, ?_, ?_, rfl⟩ <;> simp



lemma distance_bounds (g : SmoothMetric3) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ x v : E3, c * ‖v‖ ≤ Real.sqrt (g.inner x v v) ∧
      Real.sqrt (g.inner x v v) ≤ C * ‖v‖) (x y : E3) :
    c * dist x y ≤ g.distance x y ∧ g.distance x y ≤ C * dist x y := by
  constructor
  · apply le_csInf (g.paths_nonempty x y)
    rintro l ⟨γ, hγ, hx, hy, rfl⟩
    have hdist : dist x y ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ := by
      rw [dist_eq_norm, norm_sub_rev, ← hx, ← hy,
        ← intervalIntegral.integral_deriv_eq_sub
          (fun _ _ ↦ hγ.differentiable (by norm_num) _) 
          ((hγ.continuous_deriv le_rfl).intervalIntegrable 0 1)]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    have hi : c * (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ≤ g.pathLength γ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hγ.continuous_deriv le_rfl).norm.const_mul c |>.intervalIntegrable 0 1)
        ((g.pathSpeed_continuous hγ).intervalIntegrable 0 1)
      intro t _
      exact (hb _ _).1
    exact (mul_le_mul_of_nonneg_left hdist hc.le).trans hi
  · let γ : ℝ → E3 := fun t ↦ x+t • (y-x)
    have hγ : ContDiff ℝ 1 γ := straight_smooth x y
    have hl : g.pathLength γ ≤ C * dist x y := by
      have hi : g.pathLength γ ≤ ∫ t in (0 : ℝ)..1, C * ‖y-x‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((g.pathSpeed_continuous hγ).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)
        intro t _
        have hd : deriv γ t = y-x := straight_deriv x y t
        simpa only [hd] using (hb (γ t) (deriv γ t)).2
      calc
        g.pathLength γ ≤ C * ‖y-x‖ := by
          simpa [intervalIntegral.integral_const] using hi
        _ ≤ C * dist x y := mul_le_mul_of_nonneg_left
          (by simp [dist_eq_norm, norm_sub_rev]) hC.le
    have hd := g.distance_le_pathLength hγ
    simpa [γ] using hd.trans hl



lemma complete_of_uniform_bounds (g : SmoothMetric3) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ x v : E3, c * ‖v‖ ≤ Real.sqrt (g.inner x v v) ∧
      Real.sqrt (g.inner x v v) ≤ C * ‖v‖) : g.Complete := by
  intro x hx
  have hxc : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hx (c*ε) (mul_pos hc hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hd := (g.distance_bounds hc hC hb (x m) (x n)).1
    have := hN m n hm hn
    nlinarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hxc
  refine ⟨y, ?_⟩
  have ht : Tendsto (fun n ↦ C * dist (x n) y) atTop (𝓝 0) := by
    simpa using (hy.dist (tendsto_const_nhds (x := y))).const_mul C
  exact squeeze_zero (fun _ ↦ g.distance_nonneg _ _)
    (fun n ↦ (g.distance_bounds hc hC hb (x n) y).2) ht

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI

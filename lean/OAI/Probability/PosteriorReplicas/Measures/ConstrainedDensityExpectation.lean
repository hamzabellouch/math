import OAI.Probability.PosteriorReplicas.Geometry.InverseMomentBins
import OAI.Probability.PosteriorReplicas.Geometry.SphereTubeQuantitative
import OAI.Probability.PosteriorReplicas.Measures.EqualLabelVersions

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma volume_labels_smul {k : ℕ} {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Labels k)).map (fun x => r • x) =
      ENNReal.ofReal (r⁻¹^k) • (volume : Measure (Labels k)) := by
  have he : (fun x : Labels k => r • x) = Matrix.toLin' (r • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    funext x
    simp
  rw [he, Real.map_matrix_volume_pi_eq_smul_volume_pi (by simp [hr.ne'])]
  simp [inv_pow, abs_of_pos hr]

lemma gaussian_rows_inner_le_volume {d k : ℕ} {v : Vec d} (hv : v ≠ 0) :
    (gaussianRows d k).map (fun A => fun i => ⟪v, A i⟫) ≤
      ENNReal.ofReal (‖v‖⁻¹^k) • (volume : Measure (Labels k)) := by
  rw [gaussianRows, PosteriorRegression.rows_inner_map]
  calc
    _ ≤ (volume : Measure (Labels k)).map (fun x => ‖v‖ • x) :=
      Measure.map_mono (PosteriorRegression.pi_gaussianReal_le_volume k) (by fun_prop)
    _ = _ := volume_labels_smul (norm_pos_iff.mpr hv)

lemma projected_rows_ball_bound {d k : ℕ} (U : Submodule ℝ (Vec d)) (p x : Vec d)
    (hx : U.starProjection (x-p) ≠ 0) (r : ℝ) :
    gaussianRows d k {A | labelNorm (labels (fun i => U.starProjection (A i)) x -
      labels (fun i => U.starProjection (A i)) p) < r} ≤
        ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) *
          volume {y : Labels k | labelNorm y < r} := by
  have hl (A : Rows d k) :
      labels (fun i => U.starProjection (A i)) x - labels (fun i => U.starProjection (A i)) p =
        fun i => ⟪U.starProjection (x-p), A i⟫ := by
    ext i
    change ⟪U.starProjection (A i), x⟫ - ⟪U.starProjection (A i), p⟫ = _
    rw [← inner_sub_right, U.inner_starProjection_left_eq_right, real_inner_comm]
  simp_rw [hl]
  have h := gaussian_rows_inner_le_volume (k := k) hx {y : Labels k | labelNorm y < r}
  rw [Measure.map_apply (by fun_prop) (measurableSet_lt (by fun_prop) measurable_const),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

lemma label_ball_pos {k : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure (Labels k)) {y | labelNorm y < r} := by
  rw [← euclidean_label_ball_volume (0 : Labels k) r]
  exact (isOpen_ball.measure_pos volume) (⟨0, mem_ball_self hr⟩)

lemma label_ball_ne_top {k : ℕ} (r : ℝ) :
    (volume : Measure (Labels k)) {y | labelNorm y < r} ≠ ∞ := by
  have he := euclidean_label_ball_volume (0 : Labels k) r
  rw [← he]
  exact (measure_ball_lt_top).ne

lemma expected_ballDensityVersion_le {d k : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (U : Submodule ℝ (Vec d)) (p : Vec d)
    (hnull : ∀ᵐ x ∂ν, U.starProjection (x-p) ≠ 0) :
    (∫⁻ A, ballDensityVersion ν (fun i => U.starProjection (A i))
      (labels (fun i => U.starProjection (A i)) p) ∂gaussianRows d k) ≤
        ∫⁻ x, ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) ∂ν := by
  let f : ℕ → Rows d k → ℝ≥0∞ := fun n A =>
    ((volume : Measure (Labels k)) {y | labelNorm y < (n+1:ℝ)⁻¹})⁻¹ *
      ν {x | labelNorm (labels (fun i => U.starProjection (A i)) x -
        labels (fun i => U.starProjection (A i)) p) < (n+1:ℝ)⁻¹}
  have hf (n : ℕ) : Measurable (f n) := by
    apply Measurable.const_mul
    exact measurable_measure_prodMk_left (show MeasurableSet
      {z : Rows d k × Vec d | labelNorm (labels (fun i => U.starProjection (z.1 i)) z.2 -
        labels (fun i => U.starProjection (z.1 i)) p) < (n+1:ℝ)⁻¹} by
      apply measurableSet_lt _ measurable_const
      exact continuous_labelNorm.measurable.comp (by fun_prop))
  change (∫⁻ A, liminf (fun n => f n A) atTop ∂gaussianRows d k) ≤ _
  apply (lintegral_liminf_le hf).trans
  apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  let r : ℝ := (n+1:ℝ)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  let S : Set (Rows d k × Vec d) := {z | labelNorm (labels (fun i => U.starProjection (z.1 i)) z.2 -
    labels (fun i => U.starProjection (z.1 i)) p) < r}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    exact continuous_labelNorm.measurable.comp (by fun_prop)
  have hs : (∫⁻ A, ν {x | (A,x) ∈ S} ∂gaussianRows d k) =
      ∫⁻ x, gaussianRows d k {A | (A,x) ∈ S} ∂ν := by
    exact (Measure.prod_apply (μ := gaussianRows d k) (ν := ν) hS).symm.trans
      (Measure.prod_apply_symm (μ := gaussianRows d k) (ν := ν) hS)
  calc
    _ = ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ∫⁻ x, gaussianRows d k {A | (A,x) ∈ S} ∂ν := by
      rw [← hs]
      change (∫⁻ A, ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ν (Prod.mk A ⁻¹' S) ∂gaussianRows d k) = _
      exact lintegral_const_mul _ (measurable_measure_prodMk_left hS)
    _ ≤ ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ∫⁻ x, ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) *
          volume {y : Labels k | labelNorm y < r} ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hnull] with x hx
      exact projected_rows_ball_bound U p x hx r
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop), mul_comm (∫⁻ x, _ ∂ν), ← mul_assoc,
        ENNReal.inv_mul_cancel (label_ball_pos hr).ne' (label_ball_ne_top r), one_mul]

end PosteriorReplicas
end

end OAI

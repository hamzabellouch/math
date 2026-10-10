import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.Directional

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
noncomputable def coordinateSeminorm (f : E → X) (x : E) (q : ℕ) : Seminorm ℝ E :=
  (normSeminorm ℝ ℝ).comp (fderiv ℝ (scalarCoordinate f q) x).toLinearMap

lemma coordinateSeminorm_apply (f : E → X) (x v : E) (q : ℕ) :
    coordinateSeminorm f x q v = |fderiv ℝ (scalarCoordinate f q) x v| := rfl

lemma coordinateSeminorm_le (hf : LipschitzWith K f) (x : E) (q : ℕ) :
    coordinateSeminorm f x q ≤ K • normSeminorm ℝ E := by
  intro v
  change ‖fderiv ℝ (scalarCoordinate f q) x v‖ ≤ (K : ℝ) * ‖v‖
  exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ (scalarCoordinate_lipschitz hf q)) (norm_nonneg _))

noncomputable def metricSeminorm (f : E → X) (x : E) : Seminorm ℝ E :=
  ⨆ q : ℕ, coordinateSeminorm f x q

lemma bddAbove_coordinateSeminorm (hf : LipschitzWith K f) (x : E) :
    BddAbove (range (coordinateSeminorm f x)) :=
  ⟨K • normSeminorm ℝ E, by rintro p ⟨q,rfl⟩; exact coordinateSeminorm_le hf x q⟩

lemma metricSeminorm_apply (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v = ⨆ q : ℕ, |fderiv ℝ (scalarCoordinate f q) x v| := by
  rw [metricSeminorm, Seminorm.iSup_apply (bddAbove_coordinateSeminorm hf x)]
  rfl

lemma metricSeminorm_le (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v ≤ (K : ℝ) * ‖v‖ :=
  (ciSup_le (fun q => coordinateSeminorm_le hf x q) :
    metricSeminorm f x ≤ K • normSeminorm ℝ E) v

lemma metricSeminorm_lipschitz (hf : LipschitzWith K f) (x : E) :
    LipschitzWith K (metricSeminorm f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
  exact ((metricSeminorm f x).norm_sub_map_le_sub v w).trans (metricSeminorm_le hf x (v-w))

lemma lineSpeed_eq_metricSeminorm (hf : LipschitzWith K f) {x : E}
    (hx : ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x) (v : E) :
    lineSpeed f v x = metricSeminorm f x v := by
  rw [metricSeminorm_apply hf]
  simp only [lineSpeed, (hx _).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ae_dense_directionalSeminorm (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (metricSeminorm f x (denseSeq E j))) := by
  have hcoord : ∀ᵐ x ∂μ, ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x := by
    rw [ae_all_iff]
    exact fun q => (scalarCoordinate_lipschitz hf q).ae_differentiableAt
  have hdir : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (lineSpeed f (denseSeq E j) x)) := by
    rw [ae_all_iff]
    exact fun j => ae_hasMetricDirectionalDeriv μ hf _
  filter_upwards [hcoord, hdir] with x hx hd j
  simpa only [lineSpeed_eq_metricSeminorm hf hx] using hd j

end CAT0Fillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings
open Metric

lemma uniformly_tendsto_of_lipschitz {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {s : Set A} (hs : IsCompact s)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) l (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ x ∈ s, dist (f j x) (g x) < ε := by
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, ht, hcov⟩ := hs.finite_cover_balls hδ
  have hev : ∀ᶠ j in l, ∀ y ∈ t, dist (f j y) (g y) < ε/2 := by
    rw [ht.eventually_all]
    exact fun y hy => (Metric.tendsto_nhds.mp (hlim y (hts hy))) (ε/2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < δ := by
    rcases mem_iUnion.mp (hcov hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hball⟩
    exact ⟨y, hyt, hball⟩
  have hdr : (K : ℝ) * dist x y < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hxy (show 0 < (K : ℝ)+1 by positivity)
    have heq : ((K : ℝ)+1)*δ = ε/4 := by dsimp [δ]; field_simp
    rw [heq] at hm
    exact lt_of_le_of_lt (by nlinarith [dist_nonneg (x := x) (y := y)]) hm
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j y) + dist (f j y) (g y) + dist (g y) (g x) :=
        (dist_triangle _ (g y) _).trans (add_le_add (dist_triangle _ (f j y) _) le_rfl)
    _ < ε/4 + ε/2 + ε/4 := by
      apply add_lt_add
      · exact add_lt_add (((hf j).dist_le_mul x y).trans_lt hdr) (hj y hy)
      · rw [dist_comm]
        exact (hg.dist_le_mul x y).trans_lt hdr
    _ = ε := by ring
end CAT0Fillings

end

end OAI

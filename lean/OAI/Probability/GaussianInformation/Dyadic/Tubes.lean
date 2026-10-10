import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.GridSpread

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
section PlaneCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_affine_tube_cover (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E,
      (∀ x : E, ‖x‖ ≤ R → infDist x (V : Set E) ≤ δ → ∃ c ∈ s, dist x c ≤ 2 * δ) ∧
      (s.card : ℝ) ≤ ((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction := by
  classical
  by_cases hempty : {x : E | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ δ}.Nonempty
  · obtain ⟨x₀, hx₀n, hx₀d⟩ := hempty
    obtain ⟨v₀, hv₀V, hv₀d⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x₀
    have hn₀ : ‖v₀‖ ≤ R + δ := by
      have ht := dist_triangle v₀ x₀ 0
      rw [dist_zero_right, dist_zero_right, dist_comm v₀ x₀, ← hv₀d] at ht
      linarith
    obtain ⟨s, _, hcover, hcard⟩ := exists_ball_cover_card_le (E := V.direction)
      (R := 2 * (R + δ)) (δ := δ) (by positivity) hδ
    let f : V.direction ↪ E := ⟨fun v => (v : E) + v₀, by
      intro v w h
      exact Subtype.ext (add_right_cancel h)⟩
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hxn hxd
      obtain ⟨v, hvV, hvd⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x
      have hnv : ‖v‖ ≤ R + δ := by
        have ht := dist_triangle v x 0
        rw [dist_zero_right, dist_zero_right, dist_comm v x, ← hvd] at ht
        linarith
      let u : V.direction := ⟨v - v₀, V.vsub_mem_direction hvV hv₀V⟩
      have hnu : ‖u‖ ≤ 2 * (R + δ) := by
        change ‖v - v₀‖ ≤ _
        exact (norm_sub_le v v₀).trans (by linarith)
      obtain ⟨a, ha, hu⟩ := hcover u hnu
      refine ⟨f a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      have he : dist v (f a) = dist u a := by
        rw [dist_eq_norm, dist_eq_norm]
        change ‖v - ((a : E) + v₀)‖ = ‖(v - v₀) - (a : E)‖
        congr 1
        abel
      calc
        dist x (f a) ≤ dist x v + dist v (f a) := dist_triangle _ _ _
        _ ≤ δ + δ := add_le_add (hvd ▸ hxd) (he ▸ hu)
        _ = 2 * δ := by ring
    · simpa only [Finset.card_map, show 2 * (2 * (R + δ)) + δ = 4 * R + 5 * δ by ring] using hcard
  · refine ⟨∅, ?_, ?_⟩
    · intro x hxn hxd
      exact (hempty ⟨x, hxn, hxd⟩).elim
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity

lemma measure_affine_tube_le_of_grid {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} (hn : 0 < n) (a : α → E)
    (p : E → EuclideanSpace ℝ (Fin n)) (hp : LipschitzWith 1 p)
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (base : Fin n → ℝ) {h R δ L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hscale : 2 * δ ≤ L * (Real.sqrt n * h))
    (b : ℝ≥0∞) (hgrid : ∀ v, μ ((p ∘ a) ⁻¹' euclideanGridCell base h v) ≤ b) :
    μ {z | ‖a z‖ ≤ R ∧ infDist (a z) (V : Set E) ≤ δ} ≤
      ENNReal.ofReal (((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction) *
        ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_affine_tube_cover V hV hR hδ
  have hsub : {z | ‖a z‖ ≤ R ∧ infDist (a z) (V : Set E) ≤ δ} ⊆
      ⋃ c ∈ s, (p ∘ a) ⁻¹' closedBall (p c) (2 * δ) := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hs (a z) hz.1 hz.2
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    exact (show dist (p (a z)) (p c) ≤ dist (a z) c from by
      simpa using hp.dist_le_mul (a z) c).trans hzc
  have hball := fun c => measure_ball_le_of_grid μ hn (p ∘ a) base hh (by positivity)
    hL hscale (p c) b hgrid
  calc
    _ ≤ μ (⋃ c ∈ s, (p ∘ a) ⁻¹' closedBall (p c) (2 * δ)) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ ((p ∘ a) ⁻¹' closedBall (p c) (2 * δ)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ s, ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b :=
      Finset.sum_le_sum fun c _ => hball c
    _ = (s.card : ℝ≥0∞) *
        ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
      simp [mul_assoc]
    _ ≤ _ := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard

end PlaneCover

end RepeatedLocalization

end OAI

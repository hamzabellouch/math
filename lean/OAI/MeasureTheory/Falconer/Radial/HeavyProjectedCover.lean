import OAI.MeasureTheory.Falconer.Geometry.GridBallOverlap

namespace OAI

/-! # A finite cover of sources whose full projected local mass is heavy -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem heavy_projected_grid_cover (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (T : Set (Space (n+1))) {R δ C : ℝ} (hδ : 0 < δ)
    (hT : ∀ z ∈ T, ‖f z‖ ≤ R) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ C*δ})
    (L : ℕ) (hL : C+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P, ‖f z-p‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_ge (R/δ+1)
  let I := integerGridBox n N
  let U (q : Fin (n+1) → ℤ) : Set (Space (n+1)) :=
    {y | ‖f y-euclideanIntegerGrid δ q‖ ≤ (C+((n+1:ℕ):ℝ))*δ}
  let H := I.filter (fun q => F ≤ μ (U q))
  let P := H.image (euclideanIntegerGrid δ)
  have hm := grid_ball_heavy_card μ f hf H hδ L hL F
    (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨P,?_,?_⟩
  · intro z hz
    let q := euclideanRound δ (f z)
    have hqI : q ∈ I := euclideanRound_mem_box hδ N hN (f z) (hT z hz)
    have hclose : ‖f z-euclideanIntegerGrid δ q‖ ≤ ((n+1:ℕ):ℝ)*δ := by
      have he := euclideanRound_distance hδ (f z)
      rw [dist_eq_norm] at he
      have hd : 0 ≤ ((n+1:ℕ):ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      exact he.trans (by linarith)
    have hsub : {y | ‖f y-f z‖ ≤ C*δ} ⊆ U q := by
      intro y hy
      change ‖f y-euclideanIntegerGrid δ q‖ ≤ _
      calc
        _ ≤ ‖f y-f z‖+‖f z-euclideanIntegerGrid δ q‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C*δ+((n+1:ℕ):ℝ)*δ := add_le_add hy hclose
        _ = _ := by ring
    have hqH : q ∈ H := Finset.mem_filter.mpr ⟨hqI,(hheavy z hz).trans (measure_mono hsub)⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hqH,rfl⟩,hclose⟩
  · have hc : (P.card:ℝ≥0∞) ≤ (H.card:ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    exact (mul_le_mul' hc le_rfl).trans hm

end Falconer

end OAI

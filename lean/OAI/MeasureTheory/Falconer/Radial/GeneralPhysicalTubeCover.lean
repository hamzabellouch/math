import OAI.MeasureTheory.Falconer.Geometry.GeneralGridRounding

namespace OAI

/-! # General-dimensional physical tube covers with original point witnesses -/

namespace Falconer
open Set Metric
open scoped BigOperators
variable {n : ℕ}

theorem general_physical_tube_cover (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (e : Space (n+1) ≃L[ℝ] Space (n+1))
    (he : ‖e.toContinuousLinearMap‖ ≤ ((n+1:ℕ):ℝ)) (v : Fin (n+1) → Space (n+1))
    (hv : ∀ i, ‖v i‖ = 1)
    (haxis : ∀ i j : Fin (n+1), j ≠ i → (e.symm (v i)) j = 0)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*(C+((n+1:ℕ):ℝ)^2)+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space (n+1)),
      (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ ((n+1:ℕ):ℝ)^2*δ) ∧
      P.card^n ≤ (∏ i : Fin (n+1), (A i).card)*(2*L+1)^(n*(n+1)) := by
  classical
  let E' := e.symm '' E
  obtain ⟨N,hN⟩ := exists_nat_ge (‖e.symm.toContinuousLinearMap‖*R/δ+1)
  have hE' : ∀ y ∈ E', ‖y‖ ≤ ‖e.symm.toContinuousLinearMap‖*R := by
    rintro y ⟨x,hx,rfl⟩
    exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hE x hx) (norm_nonneg _))
  let S := roundedEuclideanGrid E' δ N
  have hclose (y : Space (n+1)) :
      dist (e y) (e (euclideanIntegerGrid δ (euclideanRound δ y))) ≤ ((n+1:ℕ):ℝ)^2*δ := by
    calc
      _ = ‖e (y-euclideanIntegerGrid δ (euclideanRound δ y))‖ := by rw [dist_eq_norm,map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖*‖y-euclideanIntegerGrid δ (euclideanRound δ y)‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ((n+1:ℕ):ℝ)*(((n+1:ℕ):ℝ)*δ/2) := by
        apply mul_le_mul he (by simpa only [dist_eq_norm] using euclideanRound_distance hδ y)
          (norm_nonneg _) (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith [sq_nonneg ((n+1:ℕ):ℝ)]
  have hgrid : ∀ i : Fin (n+1), ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)‖ ≤ (C+((n+1:ℕ):ℝ)^2)*δ := by
    intro i z hz
    obtain ⟨y,hy,hz'⟩ := roundedEuclideanGrid_original hz
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨a,ha,hta⟩ := hcover i x hx
    have hd := hclose (e.symm x)
    rw [e.apply_symm_apply,hz',dist_comm] at hd
    have herr : ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
        perpendicularPart (v i) (x-a)‖ ≤ ((n+1:ℕ):ℝ)^2*δ := by
      rw [← perpendicularPart_sub,sub_sub_sub_cancel_right]
      exact (norm_perpendicularPart_le (hv i) _).trans (by simpa only [dist_eq_norm] using hd)
    refine ⟨a,ha,?_⟩
    calc
      _ = ‖(perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
          perpendicularPart (v i) (x-a))+perpendicularPart (v i) (x-a)‖ := by congr 1; abel
      _ ≤ ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
          perpendicularPart (v i) (x-a)‖+‖perpendicularPart (v i) (x-a)‖ := norm_add_le _ _
      _ ≤ ((n+1:ℕ):ℝ)^2*δ+C*δ := add_le_add herr hta
      _ = _ := by ring
  let P := S.image (fun z => e (euclideanIntegerGrid δ z))
  refine ⟨P,?_,?_⟩
  · intro x hx
    have hy : e.symm x ∈ E' := mem_image_of_mem _ hx
    have hz : euclideanRound δ (e.symm x) ∈ S := roundedEuclideanGrid_mem hδ N hN hE' hy
    refine ⟨e (euclideanIntegerGrid δ (euclideanRound δ (e.symm x))),Finset.mem_image.mpr ⟨_,hz,rfl⟩,?_⟩
    simpa only [e.apply_symm_apply] using hclose (e.symm x)
  · have hcard : P.card ≤ S.card := Finset.card_image_le
    exact (Nat.pow_le_pow_left hcard n).trans (general_transverse_grid_count hLW hn e v A S hδ haxis L hL hgrid)

end Falconer

end OAI

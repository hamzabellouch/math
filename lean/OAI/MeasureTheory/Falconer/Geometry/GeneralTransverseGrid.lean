import OAI.MeasureTheory.Falconer.Geometry.IntegerBox
import OAI.MeasureTheory.Falconer.Geometry.TransverseGridCoordinates

namespace OAI

/-! # General-dimensional physical grid count from the precise published input -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

noncomputable def euclideanIntegerGrid (δ : ℝ) (z : Fin (n+1) → ℤ) : Space (n+1) :=
  WithLp.toLp 2 (fun j => δ*(z j:ℝ))

theorem general_transverse_grid_count (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (e : Space (n+1) ≃L[ℝ] Space (n+1))
    (v : Fin (n+1) → Space (n+1)) (A : Fin (n+1) → Finset (Space (n+1)))
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (haxis : ∀ i j : Fin (n+1), j ≠ i → (e.symm (v i)) j = 0)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*C+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin (n+1), ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)‖ ≤ C*δ) :
    S.card^n ≤ (∏ i : Fin (n+1), (A i).card)*(2*L+1)^(n*(n+1)) := by
  classical
  have hp (i : Fin (n+1)) : (S.image (dropGridCoordinate i)).card ≤ (A i).card*(2*L+1)^n := by
    apply integer_box_cover_card _ (A i) (fun a j => (e.symm a) (i.succAbove j)/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover i y hy
    refine ⟨a,ha,?_⟩
    intro j
    have hh := inverse_coordinate_tube_bound e (v i) (e (euclideanIntegerGrid δ y)) a
      (i.succAbove j) (haxis i (i.succAbove j) (Fin.succAbove_ne i j))
    rw [e.symm_apply_apply] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    change |(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ| ≤ _
    change |δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)| ≤ _ at hb
    have hd : |(δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ| ≤
        ‖e.symm.toContinuousLinearMap‖*C := by
      rw [abs_div,abs_of_pos hδ]
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    have he : (δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ =
        (y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ := by field_simp
    rwa [he] at hd
  calc
    _ ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card := hLW n hn S
    _ ≤ ∏ i : Fin (n+1), (A i).card*(2*L+1)^n := Finset.prod_le_prod (fun i _ => hp i)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]

end Falconer

end OAI

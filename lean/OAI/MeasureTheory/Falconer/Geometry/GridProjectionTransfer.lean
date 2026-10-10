import OAI.MeasureTheory.Falconer.Geometry.PlanarScalarGrid
import OAI.MeasureTheory.Falconer.Geometry.PlanarProjectionCoordinates
import OAI.MeasureTheory.Falconer.Estimates.ScalarResolution

namespace OAI

/-! Restricted projection counts through actual coordinate changes and
rounding, with all losses given by finite covering factors. -/
namespace Falconer

noncomputable def cartesianProjection (c : ℝ) (p : Space 2) : ℝ := p 0+c*p 1

 theorem cartesianProjection_grid_error {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (p : Space 2) :
    |cartesianProjection c (planarGridFloor σ p)-cartesianProjection c p| ≤ (1+|c|)*σ := by
  have h0 : |scalarGridFloor σ (p 0)-p 0| ≤ σ := by
    simpa only [abs_sub_comm] using scalarGridFloor_error hσ (p 0)
  have h1 : |scalarGridFloor σ (p 1)-p 1| ≤ σ := by
    simpa only [abs_sub_comm] using scalarGridFloor_error hσ (p 1)
  have he : cartesianProjection c (planarGridFloor σ p)-cartesianProjection c p =
      (scalarGridFloor σ (p 0)-p 0)+c*(scalarGridFloor σ (p 1)-p 1) := by
    unfold cartesianProjection planarGridFloor
    simp only [rowPoint_zero,rowPoint_one]
    ring
  rw [he]
  have hh := abs_add_le (scalarGridFloor σ (p 0)-p 0) (c*(scalarGridFloor σ (p 1)-p 1))
  rw [abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
  nlinarith

 theorem cartesianProjection_grid_cells {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (c : ℝ) (G : Finset (Space 2)) (k : ℕ) (hk : (1+|c|)*σ ≤ (k:ℝ)*δ) :
    (scalarCells δ ((G.image (planarGridFloor σ)).image (cartesianProjection c))).card ≤
      (2*k+3)*(scalarCells δ (G.image (cartesianProjection c))).card := by
  apply scalarCells_near_card_nat hδ _ _ k
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨cartesianProjection c x,Finset.mem_image_of_mem _ hx,
    (cartesianProjection_grid_error hσ c x).trans hk⟩

 theorem cartesianProjection_coordinate_image {a b y : ℝ} (hab : b ≠ a) (hyb : y ≠ b)
    (G : Finset (Space 2)) :
    (G.image (planarProjectionCoordinates a b)).image (cartesianProjection ((y-a)/(b-y))) =
      (G.image (lineParameterProjection y)).image (fun v => ((b-a)/(b-y))*v) := by
  simp only [Finset.image_image,Function.comp_def]
  apply Finset.image_congr
  intro x _
  exact planar_projection_normalized hab hyb x

 theorem cartesianProjection_coordinate_cells {δ ρ a b y : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hab : b ≠ a) (hyb : y ≠ b) (G : Finset (Space 2)) (M m : ℕ)
    (hM : |(b-a)/(b-y)| ≤ M) (hm : ρ ≤ (m:ℝ)*δ) :
    (scalarCells δ ((G.image (planarProjectionCoordinates a b)).image
      (cartesianProjection ((y-a)/(b-y))))).card ≤
        (2*M+3)*(2*m+3)*(projectionCells ρ y G).card := by
  rw [cartesianProjection_coordinate_image hab hyb]
  have hd := scalar_dilation_cells hδ (G.image (lineParameterProjection y)) M hM
  have hr := scalar_cells_resolution hδ hρ m hm (G.image (lineParameterProjection y))
  have he : scalarCells ρ (G.image (lineParameterProjection y)) = projectionCells ρ y G := by
    simp only [scalarCells,projectionCells,Finset.image_image,Function.comp_def]
  rw [he] at hr
  exact hd.trans ((Nat.mul_le_mul_left (2*M+3) hr).trans_eq (by ring))

end Falconer

end OAI

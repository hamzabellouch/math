import OAI.MeasureTheory.Falconer.Geometry.RoundedProjectionCoordinates

namespace OAI

/-! Exact edge counts and original projection bounds for the rounded
coordinate graphs, before any asymptotic loss absorption. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem roundedProjectionCoordinates_graph_count {δ σ a b : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (U A : Finset (Space 2)) (hAU : A ⊆ U) (hsep : FiniteSeparatedAt δ U) :
    let f := roundedProjectionCoordinates σ a b
    let X := (U.image f).image (fun p => p 0)
    let Y := (U.image f).image (fun p => p 1)
    (∑ x ∈ X, ((Y.filter fun y => rowPoint x y ∈ A.image f).card:ℝ)) = (A.card:ℝ) := by
  classical
  dsimp only
  rw [coordinate_graph_count]
  · rw [Finset.card_image_of_injOn
      ((roundedProjectionCoordinates_injOn hδ hσ hab ha hb hsmall U hsep).mono hAU)]
  · intro p hp
    have hpU := Finset.image_subset_image hAU hp
    exact ⟨Finset.mem_image_of_mem _ hpU,Finset.mem_image_of_mem _ hpU⟩

 theorem roundedProjectionCoordinates_projection_cells {δ σ ρ a b y : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hρ : 0 < ρ) (hab : b ≠ a) (hy : y ≠ b)
    (G : Finset (Space 2)) (k M m : ℕ)
    (hk : (1+|(y-a)/(b-y)|)*σ ≤ (k:ℝ)*δ)
    (hM : |((b-a)/(b-y))/4| ≤ M) (hm : ρ ≤ (m:ℝ)*δ) :
    (scalarCells δ ((G.image (roundedProjectionCoordinates σ a b)).image
      (cartesianProjection ((y-a)/(b-y))))).card ≤
      (2*k+3)*(2*M+3)*(2*m+3)*(projectionCells ρ y G).card := by
  rw [roundedProjectionCoordinates_image]
  have hg := cartesianProjection_grid_cells hδ hσ ((y-a)/(b-y))
    (G.image (boundedProjectionCoordinates a b)) k hk
  rw [boundedProjectionCoordinates_projection_image hab hy] at hg
  have hd := scalar_dilation_cells hδ (G.image (lineParameterProjection y)) M hM
  have hr := scalar_cells_resolution hδ hρ m hm (G.image (lineParameterProjection y))
  have he : scalarCells ρ (G.image (lineParameterProjection y)) = projectionCells ρ y G := by
    simp only [scalarCells,projectionCells,Finset.image_image,Function.comp_def]
  rw [he] at hr
  calc
    _ ≤ (2*k+3)*(scalarCells δ ((G.image (lineParameterProjection y)).image
        (fun v => (((b-a)/(b-y))/4)*v))).card := hg
    _ ≤ (2*k+3)*((2*M+3)*(scalarCells δ (G.image (lineParameterProjection y))).card) :=
      Nat.mul_le_mul_left _ hd
    _ ≤ (2*k+3)*((2*M+3)*((2*m+3)*(projectionCells ρ y G).card)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr)
    _ = _ := by ring

 theorem coordinate_graph_factor_lower {X Y G N K : ℝ}
    (hN : 0 < N) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : 0 ≤ K)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hG : G ≤ X*Y) (hlarge : N^2 ≤ K*G) :
    N ≤ K*X ∧ N ≤ K*Y := by
  have hKG := mul_le_mul_of_nonneg_left hG hK
  have h0 := mul_le_mul_of_nonneg_left hYN (mul_nonneg hK hX)
  have h1 := mul_le_mul_of_nonneg_left hXN (mul_nonneg hK hY)
  constructor
  · apply (mul_le_mul_iff_right₀ hN).1
    nlinarith
  · apply (mul_le_mul_iff_right₀ hN).1
    nlinarith

end Falconer

end OAI

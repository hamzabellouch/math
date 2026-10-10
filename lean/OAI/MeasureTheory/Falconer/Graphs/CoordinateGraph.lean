import OAI.MeasureTheory.Falconer.Geometry.PlanarScalarGrid

namespace OAI

/-! A finite planar set is exactly the edge set of its two coordinate
projections. This keeps original point counts in the dense graph reduction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_coordinates (x : Space 2) : rowPoint (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

 theorem coordinate_graph_count (X Y : Finset ℝ) (H : Finset (Space 2))
    (hcoord : ∀ p ∈ H, p 0 ∈ X ∧ p 1 ∈ Y) :
    (∑ x ∈ X, ((Y.filter fun y => rowPoint x y ∈ H).card:ℝ)) = (H.card:ℝ) := by
  classical
  let E := (X ×ˢ Y).filter fun p => rowPoint p.1 p.2 ∈ H
  have himage : E.image (fun p => rowPoint p.1 p.2) = H := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hxy).2
    · intro hp
      refine Finset.mem_image.mpr ⟨(p 0,p 1),?_,rowPoint_coordinates p⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr (hcoord p hp),by rwa [rowPoint_coordinates]⟩
  have hc : H.card = ∑ x ∈ X, (Y.filter fun y => rowPoint x y ∈ H).card := by
    calc
      H.card = (E.image (fun p => rowPoint p.1 p.2)).card := congrArg Finset.card himage.symm
      _ = E.card := Finset.card_image_of_injective _ rowPoint_pair_injective
      _ = _ := by simp only [E,Finset.card_filter,Finset.sum_product]
  rw [hc,Nat.cast_sum]

 theorem coordinate_graph_card_le (X Y : Finset ℝ) (H : Finset (Space 2))
    (hcoord : ∀ p ∈ H, p 0 ∈ X ∧ p 1 ∈ Y) : H.card ≤ X.card*Y.card := by
  have hsub : H ⊆ scalarProductPoints X Y := by
    intro p hp
    exact Finset.mem_image.mpr ⟨(p 0,p 1),Finset.mem_product.mpr (hcoord p hp),rowPoint_coordinates p⟩
  exact (Finset.card_le_card hsub).trans_eq (scalarProductPoints_card X Y)

 theorem coordinate_graph_comparable {X Y G N K : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hK : 0 ≤ K)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hG : G ≤ X*Y) (hlarge : N^2 ≤ K*G) :
    X ≤ K*Y ∧ Y ≤ K*X := by
  have hN : 0 ≤ N := hX.le.trans hXN
  have hX2 := pow_le_pow_left₀ hX.le hXN 2
  have hY2 := pow_le_pow_left₀ hY.le hYN 2
  have hKG := mul_le_mul_of_nonneg_left hG hK
  constructor
  · apply (mul_le_mul_iff_right₀ hX).1
    nlinarith
  · apply (mul_le_mul_iff_right₀ hY).1
    nlinarith

 theorem coordinate_graph_density {ρ K G H X Y : ℝ}
    (hρ : 0 ≤ ρ) (hK : 0 < K) (hlarge : X*Y ≤ K*G) (hH : ρ*G ≤ H) :
    (ρ/K)*X*Y ≤ H := by
  have hh := mul_le_mul_of_nonneg_left hlarge (div_nonneg hρ hK.le)
  have he : (ρ/K)*(K*G) = ρ*G := by field_simp
  rw [he] at hh
  convert hh.trans hH using 1; ring

end Falconer

end OAI

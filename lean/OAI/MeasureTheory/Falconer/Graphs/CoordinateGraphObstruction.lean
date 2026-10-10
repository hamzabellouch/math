import OAI.MeasureTheory.Falconer.Graphs.DenseUnbalancedGraph
import OAI.MeasureTheory.Falconer.Graphs.CoordinateGraph
import OAI.MeasureTheory.Falconer.Geometry.GridProjectionTransfer

namespace OAI

/-! The scalar obstruction applied to the actual coordinate graph of a
finite planar set. Edge density is exactly retained planar cardinality. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem coordinate_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ S → ∀ Q : ℝ, 1 ≤ Q → Q ≤ S →
      ∀ (t : ℝ) (J : Finset ℝ) (c : ℝ → ℝ) (G : Finset (Space 2))
        (H : ℝ → Finset (Space 2)),
      let X := G.image (fun p => p 0)
      let Y := G.image (fun p => p 1)
      2*κ ≤ t → t ≤ 2 → J.Nonempty → G.Nonempty →
      (X.card:ℝ) ≤ Q*(Y.card:ℝ) → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ j ∈ J, ∀ x ∈ Y.image (fun y => c j*y),
        ∀ y ∈ Y.image (fun y => c j*y), x ≠ y → δ ≤ |x-y|) →
      (∀ j ∈ J, c j ≠ 0 ∧ |c j| ≤ M ∧ |(c j)⁻¹| ≤ M) →
      (∀ j ∈ J, H j ⊆ G) →
      (∀ j ∈ J, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, ((scalarCells δ ((H j).image (cartesianProjection (c j)))).card:ℝ) ≤ S*(X.card:ℝ)) →
      NormalizedFiniteBallBound δ t S G →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass (J.image c) u r ≤ S*r^(2*κ)*((J.image c).card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := dense_unbalanced_graph_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro M hM hMS Q hQ hQS t J c G H ht ht2 hJ hG hXY hXbound hXsep hYsep hcYsep
    hc hHG hdense hD hreg hball hlog
  let δ := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let g := Function.invFunOn c (J:Set ℝ)
  have hg : ∀ i ∈ J.image c, g i ∈ J ∧ c (g i) = i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact Function.invFunOn_pos (f := c) (s := (J:Set ℝ)) ⟨j,hj,rfl⟩
  let e := fun i x y => rowPoint x y ∈ H (g i)
  let D := fun i => scalarCells δ ((H (g i)).image (cartesianProjection i))
  have hS : 1 ≤ S := Real.one_le_exp_iff.mpr (by positivity)
  have hcount : ∀ j ∈ J,
      (∑ x ∈ X, ((Y.filter fun y => rowPoint x y ∈ H j).card:ℝ)) = ((H j).card:ℝ) := by
    intro j hj
    apply coordinate_graph_count
    intro p hp
    have hpG := hHG j hj hp
    exact ⟨Finset.mem_image_of_mem _ hpG,Finset.mem_image_of_mem _ hpG⟩
  apply hmain N hN M hM hMS Q hQ hQS t (J.image c) X Y e D G ht ht2
    (hJ.image c) (hG.image _) (hG.image _) hXY hXbound hXsep hYsep
  · intro i hi
    have he := (hg i hi).2
    rw [← he]
    exact hcYsep _ (hg i hi).1
  · intro i hi
    have he := (hg i hi).2
    rw [← he]
    exact hc _ (hg i hi).1
  · intro i hi
    have hh := (hdense _ (hg i hi).1).trans_eq (hcount _ (hg i hi).1).symm
    simpa only [e] using hh
  · intro i hi x hx y hy he
    change ⌊(x+i*y)/δ⌋ ∈ scalarCells δ ((H (g i)).image (cartesianProjection i))
    apply Finset.mem_image.mpr
    refine ⟨x+i*y,?_,rfl⟩
    exact Finset.mem_image.mpr ⟨rowPoint x y,he,by
      simp only [cartesianProjection,rowPoint_zero,rowPoint_one]⟩
  · intro i hi
    simpa only [D,(hg i hi).2] using hD _ (hg i hi).1
  · exact hreg
  · intro i hi x hx y hy he
    exact hHG _ (hg i hi).1 he
  · have hcountG : (G.card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by
      exact_mod_cast coordinate_graph_card_le X Y G (fun p hp =>
        ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩)
    have hm := mul_le_mul_of_nonneg_right hS (mul_nonneg
      (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card))
    nlinarith
  · exact hball
  · exact hlog

end Falconer

end OAI

import Mathlib
import OAI.Geometry.HyperbolicGroups.IntegralCellularBoundary

namespace OAI

section
noncomputable section
namespace HyperbolicObstruction
namespace IntegralIncidence
variable {E V G C : Type*} [Group G]
variable (start : E × Bool → V) (voltage : E × Bool → G)
variable (hv : ∀ e, voltage (reverse e) = (voltage e)⁻¹)

namespace Polygons
variable (B : Polygons E V C)

/-- Basing a lift at the first boundary vertex fixes every corner lift. -/
def offset (c : C) (i : Fin (B.size c)) : G :=
  ((List.ofFn (fun j => voltage (B.side c j))).take i.val).prod

def liftedSide (c : G × C) (i : Fin (B.size c.2)) : G × (E × Bool) :=
  (c.1 * B.offset voltage c.2 i, B.side c.2 i)

def faceBoundary (c : G × C) : (G × E) →₀ ℤ :=
  ∑ i, edgeChain voltage (B.liftedSide voltage c i)

def d₂ : ((G × C) →₀ ℤ) →ₗ[ℤ] ((G × E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (B.faceBoundary voltage)

variable (hc : ∀ c, (List.ofFn (fun i => voltage (B.side c i))).prod = 1)

include hc in
lemma offset_next (c : C) (i : Fin (B.size c)) :
    B.offset voltage c (finRotate _ i) = B.offset voltage c i * voltage (B.side c i) :=
  group_prefix_rotate _ (hc c) i

include hc in
lemma liftedSide_closed (c : G × C) (i : Fin (B.size c.2)) :
    liftedStart B.start (B.liftedSide voltage c (finRotate _ i)) =
      liftedStart B.start (liftedReverse voltage (B.liftedSide voltage c i)) := by
  apply Prod.ext
  · exact (congrArg (c.1 * ·) (B.offset_next voltage hc c.2 i)).trans
      (mul_assoc _ _ _).symm
  · exact B.closed c.2 i

include hv hc in
lemma boundary_faceBoundary (c : G × C) :
    d₁ B.start voltage (B.faceBoundary voltage c) = 0 := by
  simp only [faceBoundary,map_sum,boundary_edgeChain _ _ hv]
  have he (i : Fin (B.size c.2)) := B.liftedSide_closed voltage hc c i
  simp_rw [← he]
  rw [Finset.sum_sub_distrib]
  have hsum := Equiv.sum_comp (finRotate (B.size c.2))
    (fun i => Finsupp.single (liftedStart B.start (B.liftedSide voltage c i)) (1 : ℤ))
  rw [hsum,sub_self]

include hv hc in
/-- The independently indexed lifted integral incidence is a chain complex. -/
theorem boundary_boundary (z : (G × C) →₀ ℤ) :
    d₁ B.start voltage (B.d₂ voltage z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add,hx,hy]
  | single c a =>
      simp only [d₂,Finsupp.linearCombination_single,map_smul]
      rw [B.boundary_faceBoundary voltage hv hc,smul_zero]

include hv hc in
lemma d₁_comp_d₂ : (d₁ B.start voltage).comp (B.d₂ voltage) = 0 := by
  apply LinearMap.ext
  intro z
  exact B.boundary_boundary voltage hv hc z

end Polygons
end IntegralIncidence
end HyperbolicObstruction
end
end

section

end

end OAI

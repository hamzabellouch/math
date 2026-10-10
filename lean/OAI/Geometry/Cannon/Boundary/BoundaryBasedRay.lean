import Mathlib
import OAI.Geometry.Cannon.Flows.Node

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open Set Metric

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryBasedRaySetoid : Setoid (BasedRay D) := raySetoid D

def boundaryBasedRay (x : Boundary D) : BasedRay D := Classical.choose (Quotient.exists_rep x)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma boundaryBasedRay_rep (x : Boundary D) : Quotient.mk' (boundaryBasedRay D x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

def boundaryExpansion (x : Boundary D) (k : ℕ) : Boundary D ≃ₜ Boundary D :=
  boundaryHomeomorph D ⟨δ,hδ⟩ ((boundaryBasedRay D x).val k)⁻¹

lemma boundaryExpansion_formula (x : Boundary D) (k : ℕ) :
    let _ := visualMetricSpace D hδ
    Expansion (boundaryExpansion D hδ x k) x ((Real.exp (2*visualExponent δ)^k)⁻¹)
      (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
      (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  have hscale : (Real.exp (2*visualExponent δ)^k)⁻¹ = visualScale δ k := by
    rw [visualScale_eq_pow,Real.exp_neg,inv_pow]
  rw [hscale]
  intro y z
  have hh := visual_expansion_ray D hδ (boundaryBasedRay D x) k y z
  rw [boundaryBasedRay_rep D x] at hh
  have heq (z : Boundary D) : (boundaryExpansion D hδ x k) z =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D x).val k)⁻¹ z := rfl
  rw [heq y,heq z]
  exact ⟨hh.1,by simpa only [mul_assoc] using hh.2⟩

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

lemma boundary_smallball_expansion :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ o : Boundary D, ∀ l : ℕ, ∃ h : Boundary D → Boundary D, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ CE/(a^l)⁻¹*dist u v ∧
        (1/(LE*3^2))/(a^l)⁻¹*dist u v ≤ dist (h u) (h v) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro o l
  refine ⟨boundaryExpansion D hδ o l,(boundaryExpansion D hδ o l).continuous,?_⟩
  intro u v hu hv
  apply expansion_ball_bounds (boundaryExpansion D hδ o l) o _ _ _ 3
    (by positivity) (by positivity) (by norm_num) (boundaryExpansion_formula D hδ o l) u v hu hv

end CannonRelease

end
end
end
end
end
end
end
end
end

end OAI

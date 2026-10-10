import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Bounded currying for two discrete group coordinates -/

namespace KadisonKastler

noncomputable section

open scoped BoundedContinuousFunction

variable {G H E : Type*} [TopologicalSpace G] [TopologicalSpace H]
  [DiscreteTopology G] [DiscreteTopology H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

def boundedFamilyRow (F : (G × H) →ᵇ E) (g : G) : H →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun h => F (g, h)) ‖F‖
    (fun h => F.norm_coe_le_norm (g, h))

omit [DiscreteTopology G] [NormedSpace ℂ E] in
@[simp]
theorem boundedFamilyRow_apply (F : (G × H) →ᵇ E) (g : G) (h : H) :
    boundedFamilyRow F g h = F (g, h) := rfl

omit [DiscreteTopology G] [NormedSpace ℂ E] in
theorem boundedFamilyRow_norm_le (F : (G × H) →ᵇ E) (g : G) :
    ‖boundedFamilyRow F g‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr (fun h => F.norm_coe_le_norm (g, h))

def boundedFamilyCurry (F : (G × H) →ᵇ E) : G →ᵇ H →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (boundedFamilyRow F) ‖F‖
    (boundedFamilyRow_norm_le F)

omit [NormedSpace ℂ E] in
@[simp]
theorem boundedFamilyCurry_apply (F : (G × H) →ᵇ E) (g : G) :
    boundedFamilyCurry F g = boundedFamilyRow F g := rfl

def boundedFamilyCurryL : ((G × H) →ᵇ E) →L[ℂ] (G →ᵇ H →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := boundedFamilyCurry
      map_add' F K := by ext g h; rfl
      map_smul' c F := by ext g h; rfl }
    1 (fun F => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
        (boundedFamilyRow_norm_le F))

@[simp]
theorem boundedFamilyCurryL_apply (F : (G × H) →ᵇ E) (g : G) (h : H) :
    boundedFamilyCurryL F g h = F (g, h) := rfl

end

end KadisonKastler

end OAI

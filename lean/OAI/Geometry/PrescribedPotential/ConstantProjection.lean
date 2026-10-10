import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalPartition

namespace OAI

/-! Constant Projection. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  {A : ComplexAtlas d X}

def Smooth.constLinear : ℂ →ₗ[ℝ] Smooth A where
  toFun := Smooth.const
  map_add' := by intro c e; rfl
  map_smul' := by intro c e; rfl

namespace Localizers
variable [T2Space X] [CompactSpace X] {ι : Type*} [Fintype ι] (D : Localizers A ι)

def constants : ℂ →L[ℝ] D.Sobolev 0 :=
  LinearMap.toContinuousLinearMap ((D.embed 0).comp Smooth.constLinear)

@[simp] lemma constants_apply (c : ℂ) :
    D.constants c = D.embed 0 (Smooth.const c) := rfl

 
structure ConstantProjection where
  proj : D.Sobolev 0 →L[ℝ] D.Sobolev 0
  compact : IsCompactOperator proj
  value : ∀ u, ∃ c : ℂ, proj u = D.embed 0 (Smooth.const c)
  fixed : ∀ c : ℂ, proj (D.embed 0 (Smooth.const c)) = D.embed 0 (Smooth.const c)

theorem constantProjection_exists : Nonempty D.ConstantProjection := by
  let S := (D.constants : ℂ →ₗ[ℝ] D.Sobolev 0).range
  let : FiniteDimensional ℝ S := LinearMap.finiteDimensional_range _
  obtain ⟨r, hr⟩ := Submodule.ClosedComplemented.of_finiteDimensional S
  let P := S.subtypeL ∘L r
  refine ⟨⟨P, ?_, ?_, ?_⟩⟩
  · exact ((isCompactOperator_id (E := S)).comp_clm r).clm_comp S.subtypeL
  · intro u
    obtain ⟨c, hc⟩ := (r u).property
    exact ⟨c, hc.symm⟩
  · intro c
    have hc : D.embed 0 (Smooth.const c) ∈ S := ⟨c, rfl⟩
    have h := congrArg Subtype.val (hr ⟨D.embed 0 (Smooth.const c), hc⟩)
    exact h

end Localizers
end GlobalElliptic

end
end

end OAI

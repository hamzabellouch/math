import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionGermSystem
import OAI.AlgebraicGeometry.Seshadri.Divisors.IdealSectionLifting

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullbackSection_linear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (∀ s t : (O X ⟶ L.sheaf), pullbackSection f (s+t) = pullbackSection f s + pullbackSection f t) ∧
    (∀ (c : ℂ) (s : (O X ⟶ L.sheaf)), pullbackSection f (c • s) = c • (pullbackSection f s : (O Y ⟶ (L.pullback f).sheaf))) := by
  classical
  let (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
  let (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
  let y : Y := Classical.arbitrary Y
  obtain ⟨V,hyV,⟨eV⟩,-⟩ := common_affine_frames L L (f y)
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  obtain ⟨_,⟨W,hW,rfl⟩,hyW,hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ f ⁻¹ᵁ V.1 from hyV) (f ⁻¹ᵁ V.1).isOpen
  let U : Y.affineOpens := ⟨W,hW⟩
  let eU := frameOnSmaller eF U.1 hWV
  let : Nonempty U.1 := ⟨⟨y,hyW⟩⟩
  let : Algebra ℂ Γ(X,V.1) := (openScalars g V.1).toAlgebra
  let : Algebra ℂ Γ(Y,U.1) := (openScalars h U.1).toAlgebra
  let A := affineCoefficientLinear h U eU
  let B := affineCoefficientLinear g V eV
  let F := affineMapAlgHom h g f hf V U hWV
  have hA := affineCoefficientLinear_injective h (L.pullback f) U eU
  have he (s : (O X ⟶ L.sheaf)) : A (pullbackSection f s) = F (B s) := heF U hWV s
  let := complexSectionModule g L.sheaf
  let := complexSectionModule h ((Scheme.Modules.pullback f).obj L.sheaf)
  constructor
  · intro s t
    apply hA
    change A (pullbackSection f (s+t)) = A (pullbackSection f s + pullbackSection f t)
    calc
      A (pullbackSection f (s+t)) = F (B (s+t)) := he _
      _ = F (B s + B t) := congrArg F (B.map_add s t)
      _ = F (B s) + F (B t) := map_add F _ _
      _ = A (pullbackSection f s) + A (pullbackSection f t) :=
        congrArg₂ (· + ·) (he s).symm (he t).symm
      _ = A (pullbackSection f s + pullbackSection f t) := (A.map_add _ _).symm
  · intro c s
    apply hA
    change A (pullbackSection f (c • s)) = A (c • pullbackSection f s)
    calc
      A (pullbackSection f (c • s)) = F (B (c • s)) := he _
      _ = F (c • B s) := congrArg F (B.map_smul c s)
      _ = c • F (B s) := map_smul F c (B s)
      _ = c • A (pullbackSection f s) := congrArg (c • ·) (he s).symm
      _ = A (c • pullbackSection f s) := (A.map_smul c _).symm

def pullbackSectionLinear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (O X ⟶ L.sheaf) →ₗ[ℂ] (O Y ⟶ (L.pullback f).sheaf) := by
  letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
  letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
  exact { toFun := pullbackSection f
          map_add' := (pullbackSection_linear g h f hf L).1
          map_smul' := (pullbackSection_linear g h f hf L).2 }

end
end MaximalSeshadri.Geometry

end

end OAI

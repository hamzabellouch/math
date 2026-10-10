import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Configurations.SmoothRationalPoints

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma spec_openScalars {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars f U.1)) = U.2.fromSpec ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U.1 (by simp)) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)

def affineComplexPoint {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ) :
    Over.mk (𝟙 complexBase) ⟶ Over.mk f := by
  letI := (openScalars f U.1).toAlgebra
  refine Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ U.2.fromSpec) ?_
  rw [Category.assoc,← spec_openScalars,← Spec.map_comp,← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact ρ.comp_algebraMap

lemma affineComplexPoint_factor {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (p : Over.mk (𝟙 complexBase) ⟶ Over.mk f)
    (hp : p.left (fieldPoint ℂ) ∈ U.1) :
    ∃ ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ,
      affineComplexPoint f U ρ = p := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range p.left ⊆ Set.range U.2.fromSpec := by
    rintro _ ⟨z,rfl⟩
    change Spec (CommRingCat.of ℂ) at z
    rw [show z = fieldPoint ℂ from Subsingleton.elim _ _,U.2.range_fromSpec]
    exact hp
  let l := IsOpenImmersion.lift U.2.fromSpec p.left hr
  let q := Spec.preimage l
  have hq : Spec.map q ≫ U.2.fromSpec = p.left := by
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ hr
  have hg : CommRingCat.ofHom (openScalars f U.1) ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,← Category.assoc,hq,Spec.map_id]
    exact p.w
  let ρ : Γ(X,U.1) →ₐ[ℂ] ℂ :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hg c }
  refine ⟨ρ,?_⟩
  apply Over.OverMorphism.ext
  exact hq

lemma affineComplexPoint_image_injective {X : Scheme} (f : X ⟶ complexBase)
    (U : X.affineOpens) :
    Function.Injective (fun ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ =>
      (affineComplexPoint f U ρ).left (fieldPoint ℂ)) := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  intro ρ σ h
  apply rational_kernel_injective
  exact congrArg PrimeSpectrum.asIdeal (U.2.fromSpec.isOpenEmbedding.injective h)

def affineMapAlgHom {X Y : Scheme} (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    (h : X ⟶ Y) (hh : h ≫ g = f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1) :
    letI := (openScalars f V.1).toAlgebra
    letI := (openScalars g U.1).toAlgebra
    Γ(Y,U.1) →ₐ[ℂ] Γ(X,V.1) := by
  letI := (openScalars f V.1).toAlgebra
  letI := (openScalars g U.1).toAlgebra
  have he : CommRingCat.ofHom (openScalars g U.1) ≫ h.appLE U.1 V.1 hVU =
      CommRingCat.ofHom (openScalars f V.1) := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,spec_openScalars,
      ← Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU,
      Category.assoc,hh]
  exact { (h.appLE U.1 V.1 hVU).hom with
    commutes' := fun c => CategoryTheory.congr_fun he c }

lemma affineMapAlgHom_point {X Y : Scheme}
    (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    (h : X ⟶ Y) (hh : h ≫ g = f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1)
    (ρ : letI := (openScalars f V.1).toAlgebra; Γ(X,V.1) →ₐ[ℂ] ℂ) :
    letI := (openScalars f V.1).toAlgebra
    letI := (openScalars g U.1).toAlgebra
    (affineComplexPoint g U (ρ.comp (affineMapAlgHom f g h hh U V hVU))).left =
      (affineComplexPoint f V ρ).left ≫ h := by
  let := (openScalars f V.1).toAlgebra
  let := (openScalars g U.1).toAlgebra
  change Spec.map (CommRingCat.ofHom (ρ.comp (affineMapAlgHom f g h hh U V hVU)).toRingHom) ≫
    U.2.fromSpec = (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ V.2.fromSpec) ≫ h
  rw [show CommRingCat.ofHom (ρ.comp (affineMapAlgHom f g h hh U V hVU)).toRingHom =
    h.appLE U.1 V.1 hVU ≫ CommRingCat.ofHom ρ.toRingHom from rfl,
    Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU,
    Category.assoc]
end
end MaximalSeshadri.Geometry

end


end OAI

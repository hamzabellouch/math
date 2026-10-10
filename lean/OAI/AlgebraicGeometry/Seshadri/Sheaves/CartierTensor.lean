import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Sections
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionMono

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Tensor
noncomputable section
open TensorProduct
variable {R S A B P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
  [NoZeroSMulDivisors S P]

theorem tmul_injective_of_local_coefficient (f : A →ₗ[R] S) (g : B →ₗ[R] P)
    {a : A} (ha : f a ≠ 0) (hg : Function.Injective g) :
    Function.Injective (fun b : B => a ⊗ₜ[R] b) := by
  let bil : A →ₗ[R] (B →ₗ[R] P) := {
    toFun a := f a • g
    map_add' a b := by simp only [map_add, add_smul]
    map_smul' r a := by
      ext b
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
      exact smul_assoc r (f a) (g b) }
  intro b c h
  have hh := congrArg (TensorProduct.lift bil) h
  change f a • g b = f a • g c at hh
  apply hg
  apply sub_eq_zero.mp
  apply (eq_zero_or_eq_zero_of_smul_eq_zero (c := f a) ?_).resolve_left ha
  rw [smul_sub, hh, sub_self]

end
end MaximalSeshadri.Tensor

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} (L : LineBundle X)

def frameCoefficient (T : X.Opens)
    (e : L.sheaf.restrict T.ι ≅ structureSheaf T.toScheme) (V : T.toScheme.Opens) :
    Γ(L.sheaf, T.ι ''ᵁ V) →ₗ[Γ(X, T.ι ''ᵁ V)] Γ(X, T.ι ''ᵁ V) where
  toFun m := (T.ι.appIso V).inv
    (e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv m))
  map_add' a b := by
    simp only [map_add]
    exact (T.ι.appIso V).inv.hom.map_add _ _
  map_smul' r a := by
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, e.hom.app_smul]
    let b : Γ(T.toScheme, V) := e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv a)
    have h : (T.ι.appIso V).inv.hom ((T.ι.appIso V).hom r * b) =
        r * (T.ι.appIso V).inv.hom b := by
      rw [(T.ι.appIso V).inv.hom.map_mul]
      change (T.ι.appIso V).inv ((T.ι.appIso V).hom r) * _ = _
      rw [Iso.hom_inv_id_apply]
    exact h

lemma frameCoefficient_injective (T : X.Opens)
    (e : L.sheaf.restrict T.ι ≅ structureSheaf T.toScheme) (V : T.toScheme.Opens) :
    Function.Injective (frameCoefficient L T e V) := by
  apply Function.Injective.comp
    (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).inv).injective
  apply Function.Injective.comp
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
  exact (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} [IsIntegral X]

theorem LineBundle.tmul_injective (L M : LineBundle X) (U : X.Opens) [Nonempty U]
    {a : Γ(L.sheaf, U)} (ha : a ≠ 0) :
    Function.Injective (fun b : Γ(M.sheaf, U) => a ⊗ₜ[Γ(X, U)] b) := by
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
  let W : X.Opens := T.ι ''ᵁ V
  have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
  let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
  let h : Γ(X, U) →+* Γ(X, W) := (X.presheaf.map i.op).hom
  let : Algebra Γ(X, U) Γ(X, W) := h.toAlgebra
  let : Module Γ(X, U) Γ(M.sheaf, W) := Module.compHom _ h
  let : IsScalarTower Γ(X, U) Γ(X, W) Γ(M.sheaf, W) :=
    IsScalarTower.of_compHom _ _ _
  let := M.noZeroSMulDivisors W
  let f : Γ(L.sheaf, U) →ₗ[Γ(X, U)] Γ(X, W) := {
    toFun a := frameCoefficient L T e V (L.sheaf.presheaf.map i.op a)
    map_add' a b := by simp only [map_add]
    map_smul' r a := by
      rw [L.sheaf.map_smul, LinearMap.map_smul]
      rfl }
  let g : Γ(M.sheaf, U) →ₗ[Γ(X, U)] Γ(M.sheaf, W) := {
    toFun a := M.sheaf.presheaf.map i.op a
    map_add' a b := map_add _ _ _
    map_smul' r a := M.sheaf.map_smul i r a }
  have hf : f a ≠ 0 := by
    intro hf
    apply ha
    apply L.restriction_injective i
    apply frameCoefficient_injective L T e V
    change frameCoefficient L T e V (L.sheaf.presheaf.map i.op a) = 0 at hf
    simpa only [map_zero] using hf
  exact Tensor.tmul_injective_of_local_coefficient f g hf (M.restriction_injective i)

def sectionMultiplyPresheaf (L M : LineBundle X) (s : GlobalSections X L.sheaf) :
    M.sheaf.val ⟶ PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      L.sheaf.val M.sheaf.val := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (λ_ M.sheaf.val).inv ≫ (s.val ⊗ₘ 𝟙 M.sheaf.val)

omit [IsIntegral X] in
lemma sectionMultiplyPresheaf_apply (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (U : X.Opens) (m : Γ(M.sheaf, U)) :
    (sectionMultiplyPresheaf L M s).app (Opposite.op U) m =
      s.app U (1 : Γ(X, U)) ⊗ₜ[Γ(X, U)] m := rfl

def sectionMultiply (L M : LineBundle X) (s : GlobalSections X L.sheaf) :
    M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
  ((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
    M.sheaf).inv ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (sectionMultiplyPresheaf L M s)

lemma sectionMultiplyPresheaf_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Mono (sectionMultiplyPresheaf L M s) := by
  apply PresheafOfModules.mono_of_injective
  intro U a b hab
  by_cases hU : Nonempty U.unop
  · let := hU
    have hn : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
      intro hn
      apply hs
      apply L.section_restriction_injective U.unop
      exact hn
    apply L.tmul_injective M U.unop hn
    exact hab
  · have he : U.unop = ⊥ := by
      apply Opens.ext
      ext x
      exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
    let := Module.subsingleton Γ(X, U.unop) Γ(M.sheaf, U.unop)
    change Γ(M.sheaf, U.unop) at a b
    exact Subsingleton.elim a b

theorem sectionMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Mono (sectionMultiply L M s) := by
  have : Mono (sectionMultiplyPresheaf L M s) := sectionMultiplyPresheaf_mono L M s hs
  have hm : Mono ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (sectionMultiplyPresheaf L M s)) := by
    exact CategoryTheory.preserves_mono_of_preservesLimit _ _
  let e := (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app M.sheaf
  have he : Mono e.inv := ⟨fun a b h => by
    have q := congrArg (fun k => k ≫ e.hom) h
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using q⟩
  exact mono_comp' he hm

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme} [IsIntegral X]

def cartierQuotient (L M : LineBundle X) (s : GlobalSections X L.sheaf) : X.Modules :=
  cokernel (sectionMultiply L M s)

theorem cartierSequence_exact (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (ShortComplex.mk (sectionMultiply L M s) (cokernel.π _)
      (cokernel.condition _)).ShortExact := by
  have : Mono (sectionMultiply L M s) := sectionMultiply_mono L M s hs
  exact { exact := ShortComplex.exact_cokernel _ }

theorem globalCartierDivision (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (q : GlobalSections X (moduleTensor X L.sheaf M.sheaf)) :
    (∃! t : GlobalSections X M.sheaf, t ≫ sectionMultiply L M s = q) ↔
      q ≫ cokernel.π (sectionMultiply L M s) = 0 := by
  have : Mono (sectionMultiply L M s) := sectionMultiply_mono L M s hs
  constructor
  · rintro ⟨t, rfl, _⟩
    simp only [Category.assoc, cokernel.condition, Limits.comp_zero]
  · intro hq
    refine ⟨Abelian.monoLift _ q hq, Abelian.monoLift_comp _ q hq, ?_⟩
    intro t ht
    apply (cancel_mono (sectionMultiply L M s)).mp
    rw [ht, Abelian.monoLift_comp]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI

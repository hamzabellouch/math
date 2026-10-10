import OAI.Algebra.AuslanderReiten.Ext.ExtKunneth
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainNaturality

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]

theorem homCochain_mem_cycles (n : ℕ) (f : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    f ∈ LinearMap.ker ((homCochain k R P.complex Y).d n (n+1)).hom := by
  change ((homCochain k R P.complex Y).d n (n+1)).hom f=0
  rw [homCochain_d]
  exact hf

theorem homCochainNativeExtEquiv_literal (n : ℕ)
    (f : P.complex.X n →ₗ[R] Y) (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    homCochainNativeExtEquiv k R P Y n
      (VectorCochain.literalClass k (homCochain k R P.complex Y) n ⟨f,homCochain_mem_cycles k R P Y n f hf⟩) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) f)
        (n+1) rfl (ModuleCat.hom_ext hf) := by
  let C := canonicalHomCochain k R P.complex (ModuleCat.of R Y)
  let z : LinearMap.ker (C.d n (n+1)).hom := ⟨f,by
    change (C.d n (n+1)).hom f=0
    dsimp only [C, canonicalHomCochain]
    rw [homCochain_d]
    exact hf⟩
  have hz := VectorCochain.literalClass_map k (homCochainScalarIso k R P.complex Y).hom n
    (⟨f,homCochain_mem_cycles k R P Y n f hf⟩ : LinearMap.ker ((homCochain k R P.complex Y).d n (n+1)).hom) z rfl
  change homCochainExtEquiv k R (Y := ModuleCat.of R Y) P n
    ((homologyMap (homCochainScalarIso k R P.complex Y).hom n).hom
      (VectorCochain.literalClass k (homCochain k R P.complex Y) n ⟨f,homCochain_mem_cycles k R P Y n f hf⟩)) = _
  rw [hz]
  have he := homCochainExtEquiv_cycleClass k R (Y := ModuleCat.of R Y) P n z
  erw [homCochainCycleClass_eq_literal] at he
  exact he

theorem homCochainExtEquiv_literal (N : ModuleCat.{u} R) (n : ℕ)
    (f : P.complex.X n →ₗ[R] N) (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    homCochainExtEquiv k R (Y := N) P n
      (VectorCochain.literalClass k (homCochain k R P.complex N) n
        ⟨f,homCochain_mem_cycles k R P N n f hf⟩) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := N) f)
        (n+1) rfl (ModuleCat.hom_ext hf) := by
  let z : LinearMap.ker (homShort k R (Y := N) P n).g.hom :=
    ⟨f,homCochain_mem_cycles k R P N n f hf⟩
  have he := homCochainExtEquiv_cycleClass k R (Y := N) P n z
  rw [homCochainCycleClass_eq_literal] at he
  exact he

end ArExplicit.ExternalTensor

end

end OAI

import OAI.Algebra.Finitistic.Bar.LeadingSupportedComparison
import OAI.Algebra.Finitistic.Bar.IndexedPatternEmbedding

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

def flatEmbedding (r n : ℕ) : flat (leadingBarSequence k D X r) Z (r+1) n ⟶
    ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  assemble (leadingBarSequence k D X r) Z (r+1) n ≫
    eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n

@[reassoc] theorem flatEmbedding_lof (r n : ℕ) (t : Index (r+1) n) :
    lof (leadingBarSequence k D X r) Z (r+1) n t ≫ flatEmbedding k D X N r n =
      inclusion (leadingBarSequence k D X r) Z (r+1) n t ≫
        eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
          leadingTotalEmbedding k D X N r n := by
  rw [flatEmbedding, lof_assemble_assoc]

theorem moduleSummandIso_supported (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0})
    (ht : Multibar.Indexed.tensor k D X N (moduleShapeEquiv r n t)=
      patternTerm k D X N (leadingPattern r n t.val)) :
    moduleSummandIso k D X N r n t = supportedLeadingIso k D X N r n t.val t.property ≪≫
      eqToIso (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht.symm) := by
  rw [supportedLeadingIso_eq]
  rfl

theorem flatEmbedding_supported (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    lof (leadingBarSequence k D X r) Z (r+1) n t.val ≫ flatEmbedding k D X N r n =
      (moduleSummandIso k D X N r n t).hom ≫
        ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N (moduleShapeEquiv r n t)) := by
  rw [flatEmbedding_lof]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  let p := leadingPattern r n t.val
  let s := moduleShapeEquiv r n t
  have hp : Multibar.Indexed.toList s=p := moduleShape_toList r n t
  have ht : Multibar.Indexed.tensor k D X N s=patternTerm k D X N p := by
    rw [Multibar.Indexed.tensor_toList, hp]
  have hl : p.length=r+n := supportedLeading_length r n t.val t.property
  have hs := outerInclusion_pattern k D X N s p hp ht hl
    ((moduleSummandIso k D X N r n t).hom.hom v)
  have hc : (eqToHom (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht)).hom
      ((moduleSummandIso k D X N r n t).hom.hom v) =
      (supportedLeadingIso k D X N r n t.val t.property).hom.hom v := by
    rw [moduleSummandIso_supported k D X N r n t ht]
    simp only [Iso.trans_hom, eqToIso.hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    have he := congrArg (fun f => f.hom
      ((supportedLeadingIso k D X N r n t.val t.property).hom.hom v))
      (eqToHom_trans (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht.symm)
        (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, eqToHom_refl,
      ModuleCat.hom_id, LinearMap.id_apply] using he
  rw [hc] at hs
  change _ = Multibar.Indexed.outerInclusion k D X N s ((moduleSummandIso k D X N r n t).hom.hom v)
  rw [hs]
  rcases t with ⟨⟨⟨⟨i,q⟩,hq⟩,t⟩,h⟩
  exact leadingTotalEmbedding_supported k D X N r n i q hq t h v
end DerivedBar.ParityBridge

end

end OAI

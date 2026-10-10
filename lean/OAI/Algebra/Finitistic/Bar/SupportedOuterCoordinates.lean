import OAI.Algebra.Finitistic.Bar.SupportedInnerCoordinates
import OAI.Algebra.Finitistic.Bar.LeadingTotalComparison

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
local instance supportedOuterScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance supportedOuterScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance supportedOuterIndexDecidableEq (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance supportedOuterInflatedModule : Module A N := inflatedModule D X N
local instance supportedOuterInflatedScalarTower : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The projected exterior coefficient remains D while the internal word uses
exactly the old literal pattern embedding. -/
theorem outerEmbed_freeBarPatternIso (i : ℕ) (p : List Bool)
    (v : ((barFunctor k D).obj (ModuleCat.of D (patternTerm k D X N p))).X i) :
    AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
      ((freeBarPatternIso k D X N i p).hom.hom v) =
    outerCast k D X N
      (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (outerSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p)
        ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)) := by
  suffices h : ∀ w : D ⊗[k] term k D (patternTerm k D X N p) i,
      AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
        ((termPatternIso k D X N (i+1) p).hom.hom w) =
      outerCast k D X N
        (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
        (outerSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p) w) from
    h ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] embed k D X N (List.replicate i false ++ p)
      ((termPatternIso k D X N i p).hom.hom w) =
      d ⊗ₜ[k] termCast k D X N _
        (suffixEmbed k D X N (patternTerm k D X N p) p.length (embed k D X N p) i w)
    rw [embed_termPatternIso]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerBarSuffix_canonicalLinear (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s i : ℕ) (e : V →ₗ[k] term k A N s)
    (v : ((barFunctor k D).obj (ModuleCat.of D V)).X i) :
    outerBarSuffix k D X N (ModuleCat.of D V) s i (canonicalLinear k D X N V s e) v =
      outerSuffixEmbed k D X N V s i e ((freeBarObjIso k D V i).hom.hom v) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

theorem outerBarSuffix_termCast (V : ModuleCat.{u} D) {a b : ℕ} (h : a=b)
    (i : ℕ) (e : V →ₗ[k] term k A N a)
    (v : ((barFunctor k D).obj V).X i) :
    outerBarSuffix k D X N V b i ((termCast k D X N h).comp e) v =
      outerCast k D X N (congrArg (fun n => n+i) h)
        (outerBarSuffix k D X N V a i e v) := by
  subst b
  rw [show termCast k D X N (rfl : a=a) = LinearMap.id from rfl, LinearMap.id_comp,
    outerCast_refl, LinearMap.id_apply]

omit [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
theorem freeBarPatternIso_eqToIso (V W : ModuleCat.{u} D) (h : V=W)
    (i : ℕ) (p : List Bool) :
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V p)) h)) ≪≫
        freeBarPatternIso k D X W i p =
    freeBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun V : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X V (List.replicate (i+1) false ++ p))) h) := by
  subst W
  simp
end DerivedBar.ParityBridge

end

end OAI

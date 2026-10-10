import OAI.Algebra.Finitistic.Bar.ModuleBlockIndex
import OAI.Algebra.Finitistic.Bar.FiniteSumSupport

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u
local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _

/-- The supported index change preserves the literal D/X word. -/
theorem moduleShape_toList (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    Multibar.Indexed.toList (moduleShapeEquiv r n t) = leadingPattern r n t.val := by
  simp [moduleShapeEquiv, moduleBlockEquiv, Multibar.Indexed.blockDegreeEquiv,
    pattern_moduleBlocks]

section General
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ

/-- A zero input term remains zero through every additive bar degree functor. -/
theorem summand_isZero
    (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
    [∀ r, (B r).Additive] (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (r n : ℕ) (t : Index r n) (h : IsZero (Z.X (inputDegree r t))) :
    IsZero (summand B Z r n t) := by
  induction r generalizing n with
  | zero => exact h
  | succ r ih =>
    rcases t with ⟨p,t⟩
    exact Functor.map_isZero (degreeFunctor B r p.val.1) (ih p.val.2 t h)

end General
local notation "c" => ComplexShape.down ℕ
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)

/-- Positive final input degrees contribute zero, without any assumption on X. -/
theorem moduleSummand_isZero (r n : ℕ) (t : Index (r+1) n)
    (h : inputDegree (r+1) t ≠ 0) :
    IsZero (summand (leadingBarSequence k D X r) Z (r+1) n t) :=
  summand_isZero _ Z _ _ t (HomologicalComplex.isZero_single_obj_X c 0 N _ h)

/-- Each surviving recursive-total summand is the exact previously indexed
block tensor in degree r+n; the input is the original D-module. -/
def moduleSummandIso (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    summand (leadingBarSequence k D X r) Z (r+1) n t.val ≅
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N (moduleShapeEquiv r n t)) := by
  have h : Multibar.Indexed.tensor k D X N (moduleShapeEquiv r n t) =
      patternTerm k D X N (leadingPattern r n t.val) := by
    rw [Multibar.Indexed.tensor_toList, moduleShape_toList]
  have e : summand (leadingBarSequence k D X r) Z (r+1) n t.val ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X N (leadingPattern r n t.val)) := by
    have hn : (Z).X (inputDegree (r+1) t.val) = N := by
      rw [t.property]
      rfl
    exact leadingSummandIso k D X Z r n t.val ≪≫ eqToIso
      (congrArg (fun V : ModuleCat D => ModuleCat.of D
        (D ⊗[k] patternTerm k D X V (leadingPattern r n t.val))) hn)
  exact e ≪≫ eqToIso (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) h.symm)

/-- The exact block tensor after reindexing supported summands by Shape. -/
def reindexedModuleSummandIso (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    summand (leadingBarSequence k D X r) Z (r+1) n ((moduleShapeEquiv r n).symm p).val ≅
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N p) := by
  exact moduleSummandIso k D X N r n ((moduleShapeEquiv r n).symm p) ≪≫
    eqToIso (congrArg (fun s : Multibar.Indexed.Shape (r+n) r =>
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N s))
        ((moduleShapeEquiv r n).apply_symm_apply p))

/-- All recursive-total terms are identified with the manuscript's exact finite
sum of tensor blocks. This includes discarding only proved zero input-degree terms. -/
def moduleFlatCoordinates (r n : ℕ) :
    (flatLeadingMultibar k D X Z r).X n ≅
      ModuleCat.of D (⨁ p : Multibar.Indexed.Shape (r+n) r,
        Multibar.Indexed.outerTensor k D X N p) := by
  let V := summand (leadingBarSequence k D X r) Z (r+1) n
  let P := fun t : Index (r+1) n => inputDegree (r+1) t=0
  let e := moduleShapeEquiv r n
  exact supportIso V P (moduleSummand_isZero k D X N r n) ≪≫
    (DirectSum.lequivCongrLeft D (M := fun t : {t // P t} => V t.val) e).toModuleIso ≪≫
    (DirectSum.congrLinearEquiv (fun p =>
      (reindexedModuleSummandIso k D X N r n p).toLinearEquiv)).toModuleIso

/-- The degreewise tensor-block isomorphism for the actual recursive leading total. -/
def leadingModuleCoordinates (r n : ℕ) :
    (barTotal k D (explicitMultibar k D X r Z)).X n ≅
      ModuleCat.of D (⨁ p : Multibar.Indexed.Shape (r+n) r,
        Multibar.Indexed.outerTensor k D X N p) :=
  (HomologicalComplex.eval _ c n).mapIso (flatLeadingMultibarIso k D X Z r).symm ≪≫
    moduleFlatCoordinates k D X N r n
end DerivedBar.RecursiveTotal

end

end OAI

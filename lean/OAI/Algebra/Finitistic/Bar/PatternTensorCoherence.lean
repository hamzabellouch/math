import OAI.Algebra.Finitistic.Bar.MultibarBlocks
import OAI.Algebra.Finitistic.Bar.TwoSidedBarFunctor

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The exterior D action on a literal pattern is the action on its first slot. -/
@[reducible] instance patternModule : (p : List Bool) → Module D (patternTerm k D X N p)
  | [] => inferInstanceAs (Module D N)
  | false :: p => inferInstanceAs (Module D (D ⊗[k] patternTerm k D X N p))
  | true :: p => inferInstanceAs (Module D (X ⊗[k] patternTerm k D X N p))

instance patternTower : (p : List Bool) → IsScalarTower k D (patternTerm k D X N p)
  | [] => inferInstanceAs (IsScalarTower k D N)
  | false :: p => inferInstanceAs (IsScalarTower k D (D ⊗[k] patternTerm k D X N p))
  | true :: p => inferInstanceAs (IsScalarTower k D (X ⊗[k] patternTerm k D X N p))

omit [Module D X] [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X] [Module D N] [IsScalarTower k D N] in
/-- Prefixing i D slots is literally the i-fold free bar term. -/
theorem term_pattern (i : ℕ) (p : List Bool) :
    DerivedBar.term k D (patternTerm k D X N p) i =
      patternTerm k D X N (List.replicate i false ++ p) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simpa only [DerivedBar.term, List.replicate_succ, List.cons_append, patternTerm] using
      congrArg (fun V : ModuleCat k => ModuleCat.of k (D ⊗[k] V)) ih

/-- Exterior actions agree as well as the underlying field-tensor modules. -/
def termPatternIso (i : ℕ) (p : List Bool) :
    ModuleCat.of D (DerivedBar.term k D (patternTerm k D X N p) i) ≅
      ModuleCat.of D (patternTerm k D X N (List.replicate i false ++ p)) := by
  induction i with
  | zero => exact Iso.refl _
  | succ i ih =>
    let e := ih.toLinearEquiv
    exact (AlgebraTensorModule.congr (LinearEquiv.refl D D) (e.restrictScalars k)).toModuleIso

/-- Coherence between canonical categorical scalars and supplied compatible scalars. -/
def freeBarObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (i : ℕ) :
    ((DerivedBar.barFunctor k D).obj (ModuleCat.of D V)).X i ≅
      ModuleCat.of D (DerivedBar.term k D V (i+1)) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact Iso.refl _

/-- The same coherence for arbitrary X bimodule coefficients. -/
def twoSidedBarObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (i : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj (ModuleCat.of D V)).X i ≅
      ModuleCat.of D (X ⊗[k] DerivedBar.term k D V i) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact Iso.refl _

/-- Coherence of a free bar term with a literal leading block. -/
def freeBarPatternIso (i : ℕ) (p : List Bool) :
    ((DerivedBar.barFunctor k D).obj (ModuleCat.of D (patternTerm k D X N p))).X i ≅
      ModuleCat.of D (patternTerm k D X N (List.replicate (i+1) false ++ p)) :=
  freeBarObjIso k D (patternTerm k D X N p) i ≪≫ termPatternIso k D X N (i+1) p

/-- Coherence of a two-sided bar term with its literal X and D slots. -/
def twoSidedBarPatternIso (i : ℕ) (p : List Bool) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj
      (ModuleCat.of D (patternTerm k D X N p))).X i ≅
      ModuleCat.of D (patternTerm k D X N (true :: (List.replicate i false ++ p))) :=
  twoSidedBarObjIso k D X (patternTerm k D X N p) i ≪≫
    (AlgebraTensorModule.congr (LinearEquiv.refl D X)
      ((termPatternIso k D X N i p).toLinearEquiv.restrictScalars k)).toModuleIso
end DerivedBar.Multibar

end

end OAI

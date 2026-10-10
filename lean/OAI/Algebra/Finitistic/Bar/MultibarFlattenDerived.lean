import OAI.Algebra.Finitistic.Bar.RecursiveTotalDifferential
import OAI.Algebra.Finitistic.Bar.BarAdditive
import OAI.Algebra.Finitistic.Bar.TotalBarDerived

namespace OAI
open CategoryTheory
noncomputable section
namespace DerivedBar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local notation "c" => ComplexShape.down ℕ

/-- The actual sequence of two-sided X bars, ending in one leading free D bar. -/
def leadingBarSequence (r j : ℕ) :
    ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ :=
  if j<r then BimoduleTensor.twoSidedBarFunctor k D X else barFunctor k D

instance leadingBarSequence_additive (r j : ℕ) :
    (leadingBarSequence k D X r j).Additive := by
  unfold leadingBarSequence
  split <;> infer_instance

variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)

/-- Before the final D bar, the actual recursive complexes agree. -/
theorem leadingBarSequence_prefix (r n : ℕ) (h : n≤r) :
    RecursiveTotal.iter (leadingBarSequence k D X r) Z n = explicitMultibar k D X n Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n<r := by omega
    simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, leadingBarSequence,
      ite_eq_left hn, ih (by omega), explicitMultibar,
      BimoduleTensor.explicitBarTotal, BimoduleTensor.twoSidedBarBicomplex]

/-- The final recursive total is precisely the manuscript's leading D bar. -/
theorem leadingBarSequence_total (r : ℕ) :
    RecursiveTotal.iter (leadingBarSequence k D X r) Z (r+1) =
      barTotal k D (explicitMultibar k D X r Z) := by
  simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, leadingBarSequence,
    lt_self_iff_false, ite_false, leadingBarSequence_prefix k D X Z r r le_rfl,
    barTotal, barBicomplex]

/-- Literal finite direct sums, equipped with the independently recursive bar
faces. No count differential or derived comparison is used in this definition. -/
def flatLeadingMultibar (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  RecursiveTotal.flatComplex (leadingBarSequence k D X r) Z (r+1)

/-- Chain isomorphism distributing all recursive X and leading-D totals. -/
def flatLeadingMultibarIso (r : ℕ) : flatLeadingMultibar k D X Z r ≅
    barTotal k D (explicitMultibar k D X r Z) :=
  RecursiveTotal.flattenChainIso (leadingBarSequence k D X r) Z (r+1) ≪≫
    eqToIso (leadingBarSequence_total k D X Z r)

/-- The flattened complex represents actual finite iteration of the constructed
left derived tensor. This uses the previously proved derived universal property. -/
def derivedIterateFlatIso (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (flatLeadingMultibar k D X Z r) :=
  derivedIterateLeadingBarIso k D X Z r ≪≫
    (chainQ D).mapIso (flatLeadingMultibarIso k D X Z r).symm
end DerivedBar

end

end OAI

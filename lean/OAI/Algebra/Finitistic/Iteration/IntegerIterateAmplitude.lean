import OAI.Algebra.Finitistic.Bar.SplitProjectiveTail
import OAI.Algebra.Finitistic.Iteration.FiniteIntegerIterate

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
variable (N : ModuleCat.{u} D)

abbrev resolvedModel (r : ℕ) := (tensorTotalIterate k D X r).obj
  ((ChainComplex.single₀ (ModuleCat D)).obj N)

include hg in
/-- A bounded input remains cohomologically bounded after actual derived tensor.
The input is resolved by its genuine projective bar total. -/
theorem tensor_exact_above (Z : ChainComplex (ModuleCat.{u} D) ℕ) (m : ℕ)
    (hZ : ∀ i, m < i → Z.ExactAt i) (n : ℕ) (hn : m+g+2 < n) :
    ((tensorTotalFunctor k D X).obj Z).ExactAt n := by
  apply ProjectiveTail.map_exact_tail (barTotal k D Z) (BimoduleTensor.tensorFunctor k D X)
    (m+1) g
  · intro i hi
    exact (exactAt_iff_of_quasiIsoAt (barTotalAugmentation k D Z) i).mpr (hZ i (by omega))
  · exact barTotal_projective k D Z
  · exact hg
  · omega

include hg in
/-- The actual finite iteration has an explicit finite homological support bound.
This bound has a two-degree allowance per step; no optimal upper bound is claimed. -/
theorem resolvedModel_exact_above (r n : ℕ) (hn : r*(g+2) < n) :
    (resolvedModel k D X N r).ExactAt n := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => simp at hn
    | succ n => exact ChainComplex.exactAt_succ_single_obj _ _
  | succ r ih =>
    apply tensor_exact_above k D X g hg (resolvedModel k D X N r) (r*(g+2)) ih n
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hn

def resolvedModelIso (r : ℕ) : object k D X N r ≅
    DerivedCategory.Q.obj ((integerExtension D).obj (resolvedModel k D X N r)) :=
  (chainToIntegerDerived D).mapIso
    ((derivedTensorIterateIso k D X r).app ((ChainComplex.single₀ (ModuleCat D)).obj N)) ≪≫
    (chainToIntegerDerivedIso D).app (resolvedModel k D X N r)

include hg in
/-- Actual derived tensor iterates have finite lower cohomological support over
any ring with the supplied genuine global projective-dimension bound. -/
theorem isGE_bound (r : ℕ) : (object k D X N r).IsGE (-((r*(g+2) : ℕ) : ℤ)) := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat (show i ≤ 0 by omega)
  let e := (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).mapIso
    (resolvedModelIso k D X N r) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
      ((integerExtension D).obj (resolvedModel k D X N r)) ≪≫
    integerExtensionHomologyIso D (resolvedModel k D X N r) n
  exact e.isZero_iff.mpr ((resolvedModel_exact_above k D X g hg N r n (by omega)).isZero_homology)

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

include hg in
theorem bounded_amplitude (r : ℕ) :
    (object k D X N r).IsGE (-((r*(g+2) : ℕ) : ℤ)) ∧ (object k D X N r).IsLE 0 :=
  ⟨isGE_bound k D X g hg N r, inferInstance⟩
end DerivedBar.IterateSupport

end

end OAI

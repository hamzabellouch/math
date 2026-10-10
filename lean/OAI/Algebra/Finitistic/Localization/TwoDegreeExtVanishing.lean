import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Abelian
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma pd_lt_three (X : ModuleCat.{max u v} (B P)) : HasProjectiveDimensionLT X 3 := by
  have h : projectiveDimension X ≤ (2 : ℕ) :=
    le_trans (le_iSup (fun N : ModuleCat.{max u v} (B P) => projectiveDimension N) X)
      (globalDimension_le_two P).1
  exact (projectiveDimension_le_iff X 2).mp h

/-- Actual higher Ext vanishing from the proved global-dimension bound for B. -/
theorem ext_eq_zero (X Y : ModuleCat.{max u v} (B P)) (n : ℕ) (hn : 3 ≤ n)
    (x : Ext X Y n) : x = 0 := by
  have := pd_lt_three P X
  exact x.eq_zero_of_hasProjectiveDimensionLT 3 hn

/-- In particular every possible degree-four connecting morphism is zero. -/
theorem shifted_hom_eq_zero (X Y : ModuleCat.{max u v} (B P)) (n : ℕ) (hn : 3 ≤ n)
    (f : (DerivedCategory.singleFunctor _ 0).obj X ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(n : ℤ)⟧) : f = 0 := by
  let x : Ext X Y n := Ext.homEquiv.symm f
  have h := ext_eq_zero P X Y n hn x
  have h' := congrArg (fun x : Ext X Y n => x.hom) h
  simpa only [x,Equiv.apply_symm_apply,Ext.zero_hom] using h'
end LittleFinitistic.TwoDegreeFormality

end

end OAI

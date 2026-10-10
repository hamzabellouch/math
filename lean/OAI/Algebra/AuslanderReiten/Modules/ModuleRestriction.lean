import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

open CategoryTheory
namespace ArExplicit.ModuleRestriction
universe v u u'
variable {R : Type u} {S : Type u'} [Ring R] [Ring S] (f : R →+* S)

theorem map_exact (s : ShortComplex (ModuleCat.{v} S)) (h : s.Exact) :
    (s.map (ModuleCat.restrictScalars f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

noncomputable instance preservesHomology : (ModuleCat.restrictScalars.{v} f).PreservesHomology :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 3).mp (map_exact f)

end ArExplicit.ModuleRestriction

end OAI

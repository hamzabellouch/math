import OAI.Algebra.Finitistic.Bimodule.BimoduleBarIteration

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- A support interval containing degree zero supplies the finite-total index;
this is automatic for the ordinary resolution's interval [-length,0]. -/
def zeroDegreeIndex (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper) :
    Fin ((res.data.upper-res.data.lower).toNat+1) :=
  Classical.choose (intervalDegrees_covers res.data.lower res.data.upper 0 ⟨hlo,hhi⟩)

theorem zeroDegreeIndex_eq (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper) :
    res.data.degrees (zeroDegreeIndex res hlo hhi) = 0 :=
  Classical.choose_spec (intervalDegrees_covers res.data.lower res.data.upper 0 ⟨hlo,hhi⟩)

/-- The chain stalk's integer extension is the native integer stalk. -/
def integerSingleIso (N : ModuleCat.{u} B) :
    (DerivedBar.integerQ B).obj ((ChainComplex.single₀ _).obj N) ≅
      DerivedCategory.Q.obj (singleInput B N) :=
  DerivedCategory.Q.mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 (by simp))

/-- Genuine native iteration on the native integer stalk, identified with the
actual Section 6 indexed multibar. No bar comparison is supplied as a premise. -/
def nativeStalkIndexedIso (hlo : res.data.lower ≤ 0) (hhi : 0 ≤ res.data.upper)
    (N : ModuleCat.{u} B) (r : ℕ) :
    (nativeIterate res r).obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (nativeIterate res r).mapIso (integerSingleIso N).symm ≪≫
    nativeIterateIndexedIso res (zeroDegreeIndex res hlo hhi)
      (zeroDegreeIndex_eq res hlo hhi) N r

/-- Functor iteration here is the usual repeated application of the native
integer-derived tensor on objects. -/
theorem nativeIterate_obj (r : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    (nativeIterate res r).obj Y = (res.data.derived.obj^[r]) Y := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change res.data.derived.obj ((nativeIterate res r).obj Y) = _
    rw [ih,Function.iterate_succ_apply']
end LittleFinitistic.BimoduleTotal

end

end OAI

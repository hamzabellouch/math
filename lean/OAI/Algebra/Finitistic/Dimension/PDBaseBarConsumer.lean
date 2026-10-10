import Mathlib.CategoryTheory.Abelian.Exact
import OAI.Algebra.Finitistic.Dimension.PDBarTensorComparison
import OAI.Algebra.Finitistic.Dimension.PDDerivedBarConsumer
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Restriction of scalars preserves the actual homology of a D-complex. -/
def restrictHomologyIso (C : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj C).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj (C.homology n) :=
  by
    let F : ModuleCat.{u} D ⥤ ModuleCat.{u} k := ModuleCat.restrictScalars (algebraMap k D)
    letI : F.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels F
    exact (C.sc n).mapHomologyIso F

/-- Actual nonzero D-module bar homology, with its exterior action intact,
forces the same projective-dimension lower bound over A. -/
theorem lower_bound_of_base_bar (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    r ≤ projectiveDimension (ModuleCat.of A N) := by
  apply PDTensor.lower_bound_of_nonzero_Tor (RightBase f) (PDMinimal.FiniteModule.of (k := k) (A := A) N) r n hrn
  intro hz
  have hz' := hz.of_iso ((torIsoTwoSided f N n) ≪≫
    restrictHomologyIso (DerivedBar.twoSidedComplex k A D N f) n).symm
  apply h
  have hs := (ModuleCat.isZero_iff_subsingleton (R := k)).mp hz'
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

abbrev baseDerived := DerivedCategory.Q.obj
  ((DerivedBar.twoSidedComplex k A D N f).extend ComplexShape.embeddingDownNat)

def baseDerivedHomologyIso (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj (baseDerived f N) ≅
      (DerivedBar.twoSidedComplex k A D N f).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app _ ≪≫
    (DerivedBar.twoSidedComplex k A D N f).extendHomologyIso ComplexShape.embeddingDownNat rfl

/-- Consumer of an actual D-linear derived bar splitting. No splitting or
nonzero-iterate theorem is assumed implicitly; the iso, retract and class are inputs. -/
theorem lower_bound_of_base_derived_retract
    (Z T : DerivedCategory (ModuleCat.{u} D)) (e : baseDerived f N ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension (ModuleCat.of A N) := by
  apply lower_bound_of_base_bar f N r n hrn
  intro hz
  let F := DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))
  have hz' : IsZero (F.obj Z) := hz.of_iso (F.mapIso e.symm ≪≫ baseDerivedHomologyIso f N n)
  apply h
  apply (IsZero.iff_id_eq_zero _).mpr
  have he : F.map i ≫ F.map p = 𝟙 (F.obj T) := by rw [← F.map_comp, hip, F.map_id]
  rw [← he, hz'.eq_of_tgt (F.map i) 0, zero_comp]
end LittleFinitistic.PDBarQuotient

end

end OAI

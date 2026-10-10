import OAI.Algebra.Finitistic.Localization.BoundedDerivedEmbedding
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Algebra

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.VectorComplexFormality
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k]

/-- A graded vector space regarded as a complex with zero differential. -/
def zeroComplex (V : ℤ → ModuleCat.{v} k) : CochainComplex (ModuleCat.{v} k) ℤ where
  X := V
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def homologySection (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    C.homology i ⟶ C.cycles i := by
  haveI : Projective (C.homology i) := ModuleCat.projective_of_categoryTheory_projective _
  exact Projective.factorThru (𝟙 _) (C.homologyπ i)

lemma homologySection_comp (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    homologySection C i ≫ C.homologyπ i = 𝟙 _ := by
  have : Projective (C.homology i) := ModuleCat.projective_of_categoryTheory_projective _
  exact Projective.factorThru_comp (𝟙 _) (C.homologyπ i)

/-- Choose cycle representatives for each homology vector space. -/
def formalityMap (C : CochainComplex (ModuleCat.{v} k) ℤ) :
    zeroComplex (fun i => C.homology i) ⟶ C where
  f i := homologySection C i ≫ C.iCycles i
  comm' i j _ := by
    change (homologySection C i ≫ C.iCycles i) ≫ C.d i j = 0 ≫ _
    rw [Category.assoc, C.iCycles_d, Limits.comp_zero, Limits.zero_comp]

lemma formality_cycles (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    cyclesMap (formalityMap C) i = (zeroComplex (fun i => C.homology i)).iCycles i ≫ homologySection C i := by
  apply (cancel_mono (C.iCycles i)).mp
  erw [cyclesMap_i, Category.assoc]
  rfl

lemma formality_homology (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    (zeroComplex (fun i => C.homology i)).homologyπ i ≫ homologyMap (formalityMap C) i =
      (zeroComplex (fun i => C.homology i)).iCycles i := by
  erw [homologyπ_naturality, formality_cycles, Category.assoc, homologySection_comp]
  exact Category.comp_id _

instance formalityMapQuasiIso (C : CochainComplex (ModuleCat.{v} k) ℤ) :
    QuasiIso (formalityMap C) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := (zeroComplex (fun i => C.homology i)).isIso_homologyπ (i-1) i (by simp) rfl
  apply (isIso_comp_left_iff ((zeroComplex (fun i => C.homology i)).homologyπ i)
    (homologyMap (formalityMap C) i)).mp
  erw [formality_homology C i]
  exact (zeroComplex (fun i => C.homology i)).isIso_iCycles i (i+1) (by simp) rfl

lemma homology_finite (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ)
    [Module.Finite k (C.X i)] : Module.Finite k (C.homology i) := by
  have : Module.Finite k (C.cycles i) := Module.Finite.of_injective (C.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma zeroHomology_property (C : CochainComplex (ModuleCat.{v} k) ℤ) (hC : ComplexProperty k C) :
    ComplexProperty k (zeroComplex (fun i => C.homology i)) := by
  obtain ⟨⟨a,b,hb⟩,hf⟩ := hC
  constructor
  · exact ⟨a,b,fun i hi => (HomologicalComplex.ExactAt.of_isZero (hb i hi)).isZero_homology⟩
  · intro i
    have := (hf i).1
    exact ⟨homology_finite C i, ModuleCat.projective_of_categoryTheory_projective _⟩

/-- The bounded homology representative has the same finite support and finite terms. -/
def zeroHomologyK (T : K.{u,v} k) : K.{u,v} k :=
  ⟨(HomotopyCategory.quotient _ _).obj (zeroComplex (fun i => T.obj.as.homology i)),
    zeroHomology_property T.obj.as T.property⟩

/-- Every bounded complex of vector spaces is isomorphic to its homology with zero differential. -/
def formalityIso (T : K.{u,v} k) : zeroHomologyK T ≅ T := by
  let C := T.obj.as
  let H := zeroComplex (fun i => C.homology i)
  let e : (derivedEmbedding k).obj (zeroHomologyK T) ≅ (derivedEmbedding k).obj T :=
    (DerivedCategory.quotientCompQhIso _).app H ≪≫
      asIso (DerivedCategory.Q.map (formalityMap C)) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app C).symm
  exact (derivedEmbedding k).preimageIso e
end LittleFinitistic.VectorComplexFormality

end

end OAI

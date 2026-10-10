import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedTruncation
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open DerivedCategory

abbrev t := (DerivedCategory.TStructure.t : CategoryTheory.Triangulated.TStructure (DerivedCategory C))
abbrev lower (X : DerivedCategory C) := (t.truncLT 0).obj X
abbrev upper (X : DerivedCategory C) := (t.truncGE 0).obj X
abbrev inclusion (X : DerivedCategory C) := (t.truncLTι 0).app X
abbrev projection (X : DerivedCategory C) := (t.truncGEπ 0).app X
abbrev triangle (X : DerivedCategory C) := (t.triangleLTGE 0).obj X
instance lower_isLE_minus_one (X : DerivedCategory C) : (lower X).IsLE (-1) :=
  t.isLE_truncLT_obj X 0 (-1) (by omega)
lemma distinguished (X : DerivedCategory C) : triangle X ∈ distTriang _ :=
  t.triangleLTGE_distinguished 0 X

lemma lower_homology_isIso (X : DerivedCategory C) (n : ℤ) (hn : n < 0) :
    IsIso ((homologyFunctor C n).map (inclusion X)) := by
  have h₀ := DerivedCategory.isZero_of_isGE (upper X) 0 n hn
  have h₁ := DerivedCategory.isZero_of_isGE (upper X) 0 (n-1) (by omega)
  have : Mono ((homologyFunctor C n).map (inclusion X)) :=
    (HomologySequence.exact₁ (triangle X) (distinguished X) (n-1) n (by omega)).mono_g
      (h₁.eq_of_src _ _)
  have : Epi ((homologyFunctor C n).map (inclusion X)) :=
    (HomologySequence.exact₂ (triangle X) (distinguished X) n).epi_f (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma upper_homology_isIso (X : DerivedCategory C) (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((homologyFunctor C n).map (projection X)) := by
  have h₀ := DerivedCategory.isZero_of_isLE (lower X) (-1) n (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE (lower X) (-1) (n+1) (by omega)
  have : Mono ((homologyFunctor C n).map (projection X)) :=
    (HomologySequence.exact₂ (triangle X) (distinguished X) n).mono_g (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C n).map (projection X)) :=
    (HomologySequence.exact₃ (triangle X) (distinguished X) n (n+1) rfl).epi_f
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

def lowerHomologyIso (X : DerivedCategory C) (n : ℤ) (hn : n < 0) :
    (homologyFunctor C n).obj (lower X) ≅ (homologyFunctor C n).obj X := by
  haveI := lower_homology_isIso X n hn
  exact asIso ((homologyFunctor C n).map (inclusion X))

def upperHomologyIso (X : DerivedCategory C) (n : ℤ) (hn : 0 ≤ n) :
    (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj (upper X) := by
  haveI := upper_homology_isIso X n hn
  exact asIso ((homologyFunctor C n).map (projection X))

/-- The exact cohomological support hypothesis in Section 4. -/
def TwoDegrees (X : DerivedCategory C) : Prop :=
  ∀ n : ℤ, n ≠ 0 → n ≠ -3 → IsZero ((homologyFunctor C n).obj X)

lemma isLE_zero (X : DerivedCategory C) (hX : TwoDegrees X) : X.IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact hX n (by omega) (by omega)
lemma isGE_neg_three (X : DerivedCategory C) (hX : TwoDegrees X) : X.IsGE (-3) := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact hX n (by omega) (by omega)
lemma lower_isGE (X : DerivedCategory C) (hX : TwoDegrees X) : (lower X).IsGE (-3) := by
  have := isGE_neg_three X hX
  infer_instance
lemma lower_isLE (X : DerivedCategory C) (hX : TwoDegrees X) : (lower X).IsLE (-3) := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  by_cases hn₀ : n < 0
  · exact (lowerHomologyIso X n hn₀).isZero_iff.mpr (hX n (by omega) (by omega))
  · exact DerivedCategory.isZero_of_isLE (lower X) (-1) n (by omega)
lemma upper_isLE (X : DerivedCategory C) (hX : TwoDegrees X) : (upper X).IsLE 0 := by
  have := isLE_zero X hX
  infer_instance

/-- An object concentrated in one degree is the stalk of its actual cohomology. -/
def singleIso (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) := Classical.choice (by
  obtain ⟨Y,⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let h : (homologyFunctor C n).obj X ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app Y
  exact ⟨e ≪≫ (singleFunctor C n).mapIso h.symm⟩)
end LittleFinitistic.DerivedTruncation

end

end OAI

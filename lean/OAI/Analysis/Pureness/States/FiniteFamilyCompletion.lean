import OAI.Analysis.Pureness.States.FiniteFamilyBounds
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFunctor
import OAI.Analysis.Pureness.States.QuotientAWStar
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFinite

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

abbrev CauchyLevel (n : ℕ) :=
  (F.positiveLevel hmono (n+1)).CauchyQuotient (F.positiveLevel_metricSize_add hmono (n+1))

def cauchyEmbedding (n : ℕ) : FinMatrix A (n+1) →⋆ₐ[ℂ] F.CauchyLevel hmono n :=
  (F.positiveLevel hmono (n+1)).quotientEmbedding (F.positiveLevel_metricSize_add hmono (n+1))

def cauchyValue (n : ℕ) : F.CauchyLevel hmono n → ℂ :=
  (F.positiveLevel hmono (n+1)).quotientValue
    (F.positiveLevel_metricSize_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (n+1))

lemma cauchyValue_embedding (n : ℕ) (x : FinMatrix A (n+1)) :
    F.cauchyValue hmono n (F.cauchyEmbedding hmono n x)=F.level (n+1) x :=
  ((F.positiveLevel hmono (n+1)).quotientValue_embedding _ _ x).trans
    ((F.level (n+1)).toPositiveQuasitrace_complexValue (hmono (n+1)) x)

def cauchyPositiveQuasitrace (n : ℕ) : PositiveQuasitrace (F.CauchyLevel hmono n) :=
  (F.positiveLevel hmono (n+1)).quotientPositiveQuasitrace
    (F.positiveLevel_metricSize_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (n+1))

def cauchyQuasitrace (n : ℕ) : ComplexQuasitrace (F.CauchyLevel hmono n) :=
  (F.cauchyPositiveQuasitrace hmono n).toComplex

lemma cauchyQuasitrace_eq (n : ℕ) (x : F.CauchyLevel hmono n) :
    F.cauchyQuasitrace hmono n x=F.cauchyValue hmono n x :=
  (F.positiveLevel hmono (n+1)).quotientComplexQuasitrace_eq _ _ x

lemma cauchyValue_faithful (n : ℕ) (x : F.CauchyLevel hmono n) :
    F.cauchyValue hmono n (star x*x)=0 ↔ x=0 :=
  (F.positiveLevel hmono (n+1)).quotientValue_square_eq_zero_iff _ _ x

theorem cauchyLevel_finite (n : ℕ) (x : F.CauchyLevel hmono n) (hx : star x*x=1) : x*star x=1 :=
  (F.positiveLevel hmono (n+1)).cauchyQuotient_isometry_unitary
    (F.positiveLevel_metricSize_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (n+1)) x hx

theorem cauchyLevel_annihilator (n : ℕ) (S : Set (F.CauchyLevel hmono n)) :
    ∃ p : F.CauchyLevel hmono n, IsStarProjection p ∧
      ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z :=
  (F.positiveLevel hmono (n+1)).quotient_right_annihilator_projection
    (F.positiveLevel_metricSize_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (n+1)) S

def cauchyInclusion {n m : ℕ} (h : n ≤ m) :
    F.CauchyLevel hmono n →⋆ₙₐ[ℂ] F.CauchyLevel hmono m :=
  PositiveQuasitrace.quotientFunctor _ _
    (F.positiveLevel_metricSize_add hmono (n+1)) (F.positiveLevel_metricSize_add hmono (m+1))
    (matrixInclusion (Nat.add_le_add_right h 1))
    (F.positiveLevel_inclusion hmono (Nat.add_le_add_right h 1))

lemma cauchyInclusion_embedding {n m : ℕ} (h : n ≤ m) (x : FinMatrix A (n+1)) :
    F.cauchyInclusion hmono h (F.cauchyEmbedding hmono n x)=
      F.cauchyEmbedding hmono m (matrixInclusion (Nat.add_le_add_right h 1) x) := rfl

lemma cauchyInclusion_value {n m : ℕ} (h : n ≤ m) (x : F.CauchyLevel hmono n) :
    F.cauchyValue hmono m (F.cauchyInclusion hmono h x)=F.cauchyValue hmono n x :=
  PositiveQuasitrace.quotientFunctor_value _ _ _ _ _ _
    (F.positiveLevel_sqrt_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (m+1)) x

lemma cauchyInclusion_isometry {n m : ℕ} (h : n ≤ m) : Isometry (F.cauchyInclusion hmono h) :=
  PositiveQuasitrace.quotientFunctor_isometry _ _ _ _ _ _
    (F.positiveLevel_sqrt_add hmono (n+1)) (F.positiveLevel_sqrt_add hmono (m+1))

lemma cauchyInclusion_self (n : ℕ) (x : F.CauchyLevel hmono n) :
    F.cauchyInclusion hmono (le_refl n) x=x := by
  obtain ⟨u,rfl⟩ := PositiveQuasitrace.cauchyQuotientMap_surjective _ _ x
  change PositiveQuasitrace.cauchyQuotientMap _ _ _=PositiveQuasitrace.cauchyQuotientMap _ _ u
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext k
  exact matrixPad_self _ _

lemma cauchyInclusion_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (x : F.CauchyLevel hmono n) :
    F.cauchyInclusion hmono g (F.cauchyInclusion hmono h x)=F.cauchyInclusion hmono (h.trans g) x := by
  obtain ⟨u,rfl⟩ := PositiveQuasitrace.cauchyQuotientMap_surjective _ _ x
  change PositiveQuasitrace.cauchyQuotientMap _ _ _=PositiveQuasitrace.cauchyQuotientMap _ _ _
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext l
  exact matrixInclusion_trans _ _ _
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI

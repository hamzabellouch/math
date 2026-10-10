import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFunctor
import OAI.Analysis.Pureness.States.FiniteQuasitraceCauchyValue

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
variable (hfinite : ∀ x, d x ≠ ⊤)

def finiteQuotientQuasitrace (n : ℕ) : ComplexQuasitrace (FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)).quotientComplexQuasitrace
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (n+1))
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (n+1))

lemma finiteQuotientQuasitrace_eq (n : ℕ) (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuotientQuasitrace d hd hlsc hfinite n x = finiteQuasitraceCauchyValue d hd hlsc hfinite n x :=
  PositiveQuasitrace.quotientComplexQuasitrace_eq _ _ _ x

def finiteQuotientInclusion {n m : ℕ} (h : n ≤ m) :
    FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n →⋆ₙₐ[ℂ]
      FiniteQuasitraceCauchyQuotient d hd hlsc hfinite m :=
  PositiveQuasitrace.quotientFunctor _ _
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (n+1))
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (m+1))
    (matrixInclusion (Nat.add_le_add_right h 1))
    (finiteSpectralPositiveQuasitrace_inclusion d hd hlsc hfinite (Nat.add_le_add_right h 1))

lemma finiteQuotientInclusion_embedding {n m : ℕ} (h : n ≤ m) (x : FinMatrix A (n+1)) :
    finiteQuotientInclusion d hd hlsc hfinite h (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite n x)=
      finiteQuasitraceCauchyEmbedding d hd hlsc hfinite m (matrixInclusion (Nat.add_le_add_right h 1) x) := rfl

lemma finiteQuotientInclusion_value {n m : ℕ} (h : n ≤ m)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuasitraceCauchyValue d hd hlsc hfinite m (finiteQuotientInclusion d hd hlsc hfinite h x)=
      finiteQuasitraceCauchyValue d hd hlsc hfinite n x :=
  PositiveQuasitrace.quotientFunctor_value _ _ _ _ _ _
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (n+1))
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (m+1)) x

lemma finiteQuotientInclusion_isometry {n m : ℕ} (h : n ≤ m) :
    Isometry (finiteQuotientInclusion d hd hlsc hfinite h) :=
  PositiveQuasitrace.quotientFunctor_isometry _ _ _ _ _ _
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (n+1))
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (m+1))

lemma finiteQuotientInclusion_self (n : ℕ)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuotientInclusion d hd hlsc hfinite (le_refl n) x=x := by
  obtain ⟨u,rfl⟩ := PositiveQuasitrace.cauchyQuotientMap_surjective _ _ x
  change PositiveQuasitrace.cauchyQuotientMap _ _ _=PositiveQuasitrace.cauchyQuotientMap _ _ u
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext k
  exact matrixPad_self _ _

lemma finiteQuotientInclusion_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuotientInclusion d hd hlsc hfinite g (finiteQuotientInclusion d hd hlsc hfinite h x)=
      finiteQuotientInclusion d hd hlsc hfinite (h.trans g) x := by
  obtain ⟨u,rfl⟩ := PositiveQuasitrace.cauchyQuotientMap_surjective _ _ x
  change PositiveQuasitrace.cauchyQuotientMap _ _ _=PositiveQuasitrace.cauchyQuotientMap _ _ _
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext l
  exact matrixInclusion_trans _ _ _
end CuntzPureness

end

end OAI

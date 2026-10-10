import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientValue

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped Topology NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
variable (hfinite : ∀ x, d x ≠ ⊤)

abbrev FiniteQuasitraceCauchyQuotient (n : ℕ) :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)).CauchyQuotient
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (n+1))

def finiteQuasitraceCauchyEmbedding (n : ℕ) :
    FinMatrix A (n+1) →⋆ₐ[ℂ] FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)).quotientEmbedding
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (n+1))

def finiteQuasitraceCauchyValue (n : ℕ) : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n → ℂ :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)).quotientValue
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite (n+1))
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite (n+1))

lemma finiteQuasitraceCauchyValue_embedding (n : ℕ) (x : FinMatrix A (n+1)) :
    finiteQuasitraceCauchyValue d hd hlsc hfinite n (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite n x) =
      (finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)).complexValue x :=
  PositiveQuasitrace.quotientValue_embedding _ _ _ x

lemma finiteQuasitraceCauchyValue_root_rank (n : ℕ) (M : Positive (FinMatrix A (n+1))) :
    Filter.Tendsto (fun k => ENNReal.ofReal
      (finiteQuasitraceCauchyValue d hd hlsc hfinite n
        (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite n
          (Positive.power (Positive.rootExponent k) M).1)).re) Filter.atTop
      (nhds (d (finitePositiveClass (n+1) M))) := by
  have he (k : ℕ) := finiteQuasitraceCauchyValue_embedding d hd hlsc hfinite n
    (Positive.power (Positive.rootExponent k) M).1
  simp only [he,PositiveQuasitrace.complexValue_positive,Complex.ofReal_re]
  exact finiteSpectralPositiveQuasitrace_root_rank d hd hlsc hfinite (n+1) M

lemma finiteQuasitraceCauchyValue_polar (n : ℕ) (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    finiteQuasitraceCauchyValue d hd hlsc hfinite n (star x*x) =
      finiteQuasitraceCauchyValue d hd hlsc hfinite n (x*star x) :=
  PositiveQuasitrace.quotientValue_polar _ _ _ x

open scoped ComplexOrder in
lemma finiteQuasitraceCauchyValue_square_nonneg (n : ℕ)
    (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite n) :
    0 ≤ finiteQuasitraceCauchyValue d hd hlsc hfinite n (star x*x) :=
  PositiveQuasitrace.quotientValue_square_nonneg _ _ _ x
end CuntzPureness

end

end OAI

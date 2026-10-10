import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.MatrixAlgebras
import OAI.Analysis.KadisonKastler.MatrixAveraging

namespace OAI

/-! # Projection cuts of a concrete full matrix diagonal -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} [Fintype ι] [DecidableEq ι]

/-- The projection onto a finite subset of the matrix diagonal. -/
def matrixDiagonalCut (E : MatrixUnitSystem ι (Algebra M)) (s : Finset ι) :
    AlgebraProjection M :=
  ⟨∑ i ∈ s, E.entry i i, ⟨by
    change (∑ i ∈ s, E.entry i i) * (∑ i ∈ s, E.entry i i) = ∑ i ∈ s, E.entry i i
    simp only [Finset.sum_mul, Finset.mul_sum, E.mul_entry]
    simp,
    by
      change star (∑ i ∈ s, E.entry i i) = ∑ i ∈ s, E.entry i i
      simp only [star_sum, E.star_entry]⟩⟩

theorem matrixDiagonalCut_mul_entry (E : MatrixUnitSystem ι (Algebra M))
    (s : Finset ι) (i : ι) :
    (matrixDiagonalCut E s).val * E.entry i i = if i ∈ s then E.entry i i else 0 := by
  simp [matrixDiagonalCut, Finset.sum_mul, E.mul_entry]

theorem matrixDiagonalCut_le (E : MatrixUnitSystem ι (Algebra M))
    {s t : Finset ι} (hst : s ⊆ t) : matrixDiagonalCut E s ≤ matrixDiagonalCut E t := by
  change (matrixDiagonalCut E t).val * (∑ i ∈ s, E.entry i i) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixDiagonalCut_mul_entry, ite_eq_left (hst hi)]

theorem matrixDiagonalCut_univ (E : MatrixUnitSystem ι (Algebra M)) :
    (matrixDiagonalCut E Finset.univ).val = 1 := E.total

theorem matrixDiagonalCut_mem (E : MatrixUnitSystem ι (Algebra M)) (s : Finset ι) :
    (matrixDiagonalCut E s).val ∈ E.algebra :=
  E.algebra.sum_mem (fun i _ => E.entry_mem i i)

/-- Equal diagonal traces give the exact trace of every cut. -/
theorem matrixDiagonalCut_trace (τ : TracialRepresentation M)
    (E : MatrixUnitSystem ι (Algebra M)) (c : ℂ)
    (hc : ∀ i, τ.trace (E.entry i i) = c) (s : Finset ι) :
    τ.trace (matrixDiagonalCut E s).val = (s.card : ℂ) * c := by
  change (coordinateTraceLinear τ) (∑ i ∈ s, E.entry i i) = _
  rw [map_sum]
  change (∑ i ∈ s, τ.trace (E.entry i i)) = _
  simp [hc]

end

end KadisonKastler

end OAI

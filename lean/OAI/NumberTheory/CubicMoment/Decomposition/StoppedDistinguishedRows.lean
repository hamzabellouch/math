import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedIdentity
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRowsSaving

namespace OAI

/-! Exact collection of the literal distinguished stopped coefficient into
the prime rows whose cancellation has already been proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDistinguishedRows (B ρ a b w z u : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ) (D : Finset Eisenstein)
    (v e : Eisenstein) (i : ι) : ℂ :=
  ∑ t ∈ (coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D).filter
      (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
    (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v)

theorem stoppedBeta_distinguished_rows [Nonempty ι] (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d)
    (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ i, stoppedDistinguishedRows B ρ a b w z u j j₀ k h Z Q early W D v e i := by
  rw [stoppedBeta_distinguished_original_tuple]
  congr 1
  calc
    _ = ∑ d ∈ D, ∑ i,
        ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
          if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
            (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (g l)))*
              (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
                  (∏ l, g l) d ((∏ l, g l)*(d*e)),
                cutoffMoebius primeDetectorCutoff w d*
                  distinguishedRadialWeight (W i) w z (norm p)*
                  normTwist u (((∏ l, g l)*p)*d)*cubicSymbol (((∏ l, g l)*p)*d) v)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [distinguished_tuple_stopped_rows B ρ a b j j₀ k h Z Q early d e (hD d hd)
        (fun l p => distinguishedRadialWeight (W l) w z (norm p))
        (fun n => cutoffMoebius primeDetectorCutoff w d*normTwist u n*cubicSymbol n v)]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      split_ifs
      · congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
      · rw [mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp only [stoppedDistinguishedRows, Finset.sum_filter, Finset.sum_product]

end CubicFirstMoment

end

end OAI

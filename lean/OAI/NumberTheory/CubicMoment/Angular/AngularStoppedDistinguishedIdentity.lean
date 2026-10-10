import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedIdentity
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedTupleCollection
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedTupleRows
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedComplementMass

namespace OAI

/-! The distinguished largest-prime role of literal stopped beta,
with the ordered-tuple factorial and original full-product twist. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_distinguished_original_tuple (ℓ : ℤ) (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ * ∑ d ∈ D,
      ∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
          (fun f => Squarefree ((∏ l, f l)*d)),
        if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
          if IsCoprime ((∏ l, f l)*d) e ∧
            (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (∏ l, f l) d ∧
            geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
          then (∏ l, distinguishedRadialWeight (W l) w z (norm (f l)))*
            (cutoffMoebius primeDetectorCutoff w d*normTwist u ((∏ l, f l)*d)*
              angularCubicSymbol ℓ ((∏ l, f l)*d) v) else 0
        else 0 := by
  rw [stoppedBeta_distinguished_tuple_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  have hprod : (∏ l, W l (norm (f l))*distinguishedPrimeWeight primeDetectorCutoff w z (f l)) =
      ∏ l, distinguishedRadialWeight (W l) w z (norm (f l)) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (distinguishedRadialWeight_eq_primeWeight (W l) w z (f l)).symm
  rw [hprod]
  simp only [stoppedDistinguishedTest,mul_ite,mul_zero]
  rw [←ite_and,←ite_and,←ite_and]
  have he : ((stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (∏ l, f l) d ∧ largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l) ∧
        geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j) ∧
      (Squarefree ((∏ l, f l)*d) ∧ IsCoprime ((∏ l, f l)*d) e ∧
        a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b)) ↔
    ((Squarefree ((∏ l, f l)*d) ∧
      largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l)) ∧
        (IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j)) := by tauto
  apply (if_congr he rfl rfl).trans
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI

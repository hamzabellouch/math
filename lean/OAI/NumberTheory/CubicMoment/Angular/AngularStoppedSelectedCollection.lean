import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSelectedRow
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedCollection
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedReindex

namespace OAI

/-! Exact collection of the selected-bin free-prime rows, and the
complementary norm cutoff forced by the lower endpoint of the prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_selectedStopped_row_collection (ℓ : ℤ) (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) :
    (∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w (t.2*t.1)*normTwist u (r*(t.2*t.1))*
        angularCubicSymbol ℓ (r*(t.2*t.1)) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  unfold selectedStoppedRowPairs
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrc : Squarefree (r*c) ∧ IsCoprime (r*c) e
  · simp only [hrc.1,hrc.2,true_and,ite_true]
    unfold angular_stoppedSelectedPrimeRow
    rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
      (stoppedSelectedPrimeSet_subset B ρ (a/norm (r*c)) (b/norm (r*c))
        j j₀ k h Z Q early r c e)]
  · have hzero (p : Eisenstein) :
        ¬(Squarefree (r*c) ∧ IsCoprime (r*c) e ∧
          p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
            j j₀ k h Z Q early r c e) := fun hp => hrc ⟨hp.1,hp.2.1⟩
    simp only [hzero,ite_false,Finset.sum_const_zero,hrc]


lemma angular_selectedStopped_row_eq_zero (ℓ : ℤ) {B ρ a b w u : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c v e : Eisenstein} (hr : primary r) (hc : primary c)
    (hbig : b/geometricBinLower ρ B j < norm (r*c)) :
    angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
      j j₀ k h Z Q early r c v e = 0 := by
  unfold angular_stoppedSelectedPrimeRow
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (selectedStopped_complement_bound hρ hρ₂ hj hr hc hp) hbig).elim


theorem angular_selectedStopped_original_rows (ℓ : ℤ) (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) (hr : primary r) (hbB : b ≤ B) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  rw [selectedStopped_sum_reindex B ρ a b j j₀ k h Z Q early r e hr hbB]
  exact angular_selectedStopped_row_collection ℓ B ρ a b w u j j₀ k h Z Q early r v e

end CubicFirstMoment

end

end OAI

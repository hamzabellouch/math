import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Variance
import OAI.Probability.CriticalPercolation.ProductMeasure.ClosedCutProbability

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma frequently_closedBlock_ae_of_card_le (p : unitInterval) (hp : (p:ℝ)<1)
    (S : ℕ → Set E) (hS : ∀ n, (S n).Finite)
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m))) (N : ℕ)
    (hN : ∀ n, (S n).ncard ≤ N) :
    ∀ᵐ ω ∂law (fun _ : E => p), ∃ᶠ n in atTop, ω ∈ closedBlock (S n) := by
  let A := fun n => closedBlock (S n)
  have hm' : ∀ n, MeasurableSet[blockSigma (S n)] (A n) :=
    fun n => measurableSet_closedBlock (S n) (hS n).countable
  have hm : ∀ n, MeasurableSet (A n) := fun n => blockSigma_le (S n) _ (hm' n)
  have hi := independent_block_events (fun _ : E => p) S hdis A hm'
  have hprob : ∀ n, (bitMeasure p {False})^N ≤ law (fun _ : E => p) (A n) := by
    intro n
    rw [law_closedBlock_const p (S n) (hS n)]
    exact pow_le_pow_of_le_one zero_le (prob_le_one) (hN n)
  have hsum : (∑' n, law (fun _ : E => p) (A n)) = ∞ := by
    apply top_unique
    calc
      ∞ = ∑' _n : ℕ, (bitMeasure p {False})^N :=
        (ENNReal.tsum_const_eq_top_of_ne_zero
          (pow_ne_zero _ (bitMeasure_false_ne_zero p hp))).symm
      _ ≤ _ := ENNReal.tsum_le_tsum hprob
  have hlim := measure_limsup_eq_one hm hi hsum
  have hh : ∀ᵐ ω ∂law (fun _ : E => p), ω ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hlim
  exact hh.mono (fun _ h => Filter.mem_limsup_iff_frequently_mem.mp h)

end CriticalPercolation.BernoulliProduct
end
end

end OAI

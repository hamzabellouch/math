import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma bitMeasure_false_ne_zero (p : unitInterval) (hp : (p:ℝ)<1) :
    bitMeasure p {False} ≠ 0 := by
  have hh := bitMeasure_real_singleton p False
  simp only [bitWeight,ite_false] at hh
  intro hz
  have : (bitMeasure p).real {False}=0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  linarith

theorem frequently_closedBlock_ae (p : unitInterval) (hp : (p:ℝ)<1)
    (S : ℕ → Set E) (hS : ∀ n, (S n).Finite)
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m))) (N : ℕ)
    (hN : ∀ n, (S n).ncard=N) :
    ∀ᵐ ω ∂law (fun _ : E => p), ∃ᶠ n in atTop, ω ∈ closedBlock (S n) := by
  let A := fun n => closedBlock (S n)
  have hm' : ∀ n, MeasurableSet[blockSigma (S n)] (A n) :=
    fun n => measurableSet_closedBlock (S n) (hS n).countable
  have hm : ∀ n, MeasurableSet (A n) := fun n => blockSigma_le (S n) _ (hm' n)
  have hi := independent_block_events (fun _ : E => p) S hdis A hm'
  have hprob : ∀ n, law (fun _ : E => p) (A n) = (bitMeasure p {False})^N := by
    intro n
    rw [law_closedBlock_const p (S n) (hS n),hN]
  have hsum : (∑' n, law (fun _ : E => p) (A n)) = ∞ := by
    simp_rw [hprob]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero _ (bitMeasure_false_ne_zero p hp))
  have hlim := measure_limsup_eq_one hm hi hsum
  have hl : ∀ᵐ ω ∂law (fun _ : E => p), ω ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hlim
  exact hl.mono (fun _ h => Filter.mem_limsup_iff_frequently_mem.mp h)

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI

import OAI.MathematicalPhysics.CriticalSK.ThresholdMixing

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

lemma generator_continuous {n : ℕ} : Continuous (generator (n := n)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  simp only [generator, Matrix.sum_apply, Matrix.sub_apply]
  exact continuous_finsetSum _ (fun i _ => (siteKernel_continuous i x y).sub continuous_const)

lemma discreteKernel_continuous {n : ℕ} : Continuous (discreteKernel (n := n)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  simp only [discreteKernel, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ => siteKernel_continuous i x y))

open scoped Matrix.Norms.Operator in
lemma continuousKernel_continuous {n : ℕ} (t : ℝ) :
    Continuous (fun W : Disorder n => continuousKernel W t) := by
  unfold continuousKernel
  have hexp : Continuous (NormedSpace.exp :
      Matrix (Spin n) (Spin n) ℝ → Matrix (Spin n) (Spin n) ℝ) :=
    NormedSpace.exp_continuous
  apply hexp.comp
  change Continuous ((fun _ : Disorder n => t) • generator (n := n))
  exact continuous_const.smul generator_continuous

open scoped Matrix.Norms.Operator in
lemma continuousKernel_time_continuous {n : ℕ} (W : Disorder n) :
    Continuous (continuousKernel W) := by
  unfold continuousKernel
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

lemma continuousDistance_continuous {n : ℕ} (t : ℝ) (x : Spin n) :
    Continuous (fun W : Disorder n => continuousDistance W t x) := by
  unfold continuousDistance totalVariation
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact (((continuous_apply y).comp ((continuous_apply x).comp
    (continuousKernel_continuous t))).sub (gibbs_continuous y)).abs

lemma discreteDistance_continuous {n : ℕ} (k : ℕ) (x : Spin n) :
    Continuous (fun W : Disorder n => discreteDistance W k x) := by
  unfold discreteDistance totalVariation
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact (((continuous_apply y).comp ((continuous_apply x).comp
    (discreteKernel_continuous.pow k))).sub (gibbs_continuous y)).abs

lemma continuousDistance_time_continuous {n : ℕ} (W : Disorder n) (x : Spin n) :
    Continuous (fun t : ℝ => continuousDistance W t x) := by
  unfold continuousDistance totalVariation
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact (((continuous_apply y).comp ((continuous_apply x).comp
    (continuousKernel_time_continuous W))).sub continuous_const).abs

lemma continuousMixingAt_mem {n : ℕ} (W : Disorder n) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ continuousMixingAt W ε ∧ ∀ x, continuousDistance W (continuousMixingAt W ε) x ≤ ε := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ ε} := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_id)
    change IsClosed {t : ℝ | ∀ x, continuousDistance W t x ≤ ε}
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le (continuousDistance_time_continuous W x) continuous_const
  exact hclosed.csInf_mem (continuousMixingAt_set_nonempty W hn hε) ⟨0, fun _ hs => hs.1⟩

lemma continuousMixingAt_le_iff {n : ℕ} (W : Disorder n) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    continuousMixingAt W ε ≤ t ↔ 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ ε := by
  have hm := continuousMixingAt_mem W hn hε
  constructor
  · intro ht
    exact ⟨hm.1.trans ht, fun x => (continuousDistance_antitone W hn hm.1 ht x).trans (hm.2 x)⟩
  · intro ht
    exact csInf_le ⟨0, fun _ hs => hs.1⟩ ht

lemma discreteMixingAt_le_iff {n : ℕ} (W : Disorder n) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    discreteMixingAt W ε ≤ k ↔ ∀ x, discreteDistance W k x ≤ ε := by
  constructor
  · intro hk
    have hm : ∀ x, discreteDistance W (discreteMixingAt W ε) x ≤ ε :=
      Nat.sInf_mem (discreteMixingAt_set_nonempty W hn hε)
    exact fun x => (discreteDistance_antitone W hn hk x).trans (hm x)
  · intro hk
    exact Nat.sInf_le hk

lemma continuousMixingAt_measurable {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun W : Disorder n => continuousMixingAt W ε) := by
  apply LowerSemicontinuous.measurable
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro t
  change IsClosed {W : Disorder n | continuousMixingAt W ε ≤ t}
  simp only [continuousMixingAt_le_iff _ hn hε]
  apply (show IsClosed {W : Disorder n | (0 : ℝ) ≤ t} from
    isClosed_le continuous_const continuous_const).inter
  change IsClosed {W : Disorder n | ∀ x, continuousDistance W t x ≤ ε}
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_le (continuousDistance_continuous t x) continuous_const

lemma discreteMixingAt_measurable {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun W : Disorder n => discreteMixingAt W ε) := by
  apply measurable_of_Iic
  intro k
  change MeasurableSet {W : Disorder n | discreteMixingAt W ε ≤ k}
  simp only [discreteMixingAt_le_iff _ hn hε, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  exact (isClosed_le (discreteDistance_continuous k x) continuous_const).measurableSet

end CriticalSK
end

end OAI

import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CoefficientStep
import OAI.Probability.MemoryPrecision.StochasticContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma measurable_angleTest (ε : ℝ) : Measurable (angleTest (d := d) ε) := by
  unfold angleTest
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    measurable_const measurable_const
lemma measurable_chordTest (ε : ℝ) : Measurable (chordTest (d := d) ε) := by
  apply Measurable.indicator measurable_const
  exact measurableSet_le (by fun_prop) measurable_const
lemma angleTest_le_one (ε : ℝ) (x : Sphere d × Sphere d) : angleTest ε x ≤ 1 := by
  unfold angleTest
  split <;> simp
lemma chordTest_le_one (ε : ℝ) (x : Sphere d × Sphere d) : chordTest ε x ≤ 1 := by
  exact Set.indicator_le_self' (fun _ _ => bot_le) x
lemma outputTest_measurable {f : Sphere d × Sphere d → ℝ≥0∞} (hf : Measurable f)
    (t : ℕ) (j : State M) : Measurable (K.outputTest f t j) := by
  exact (show Measurable (Function.uncurry (fun s v => f (s,v))) from hf).lintegral_prod_right
lemma outputTest_le_one {f : Sphere d × Sphere d → ℝ≥0∞} (hf : ∀ x, f x ≤ 1)
    (t : ℕ) (j : State M) (s : Sphere d) : K.outputTest f t j s ≤ 1 := by
  exact (lintegral_mono (fun v => hf (s,v))).trans_eq (by simp)

def marginal (n : ℕ) (j : State M) (obs : Vector d × ℝ) (a : State M) : ℝ≥0∞ :=
  ∑ b : Bool, K.transition n j obs (b,a)
lemma marginal_sum (n : ℕ) (j : State M) (obs : Vector d × ℝ) :
    ∑ a, K.marginal n j obs a = 1 := by
  simp only [marginal]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact K.transition_sum n j obs
lemma marginal_measurable (hK : K.Borel) (n : ℕ) (j a : State M) :
    Measurable (fun obs => K.marginal n j obs a) := by
  exact Finset.measurable_sum _ (fun b _ => hK n j (b,a))

section Evaluation
variable {X : Type*} [MeasurableSpace X]
variable (w : ℕ → State M → X → ℝ≥0∞) (ι : X → Vector d)

lemma measurable_eval (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (n k : ℕ) (j : State M) :
    Measurable (fun z : X × Observations d k => K.eval w n k j z.1 z.2) := by
  induction k generalizing n j with
  | zero => exact (hw n j).comp measurable_fst
  | succ k ih =>
    apply Finset.measurable_sum _
    intro a _
    apply ((hK (n+1) j a).comp (by fun_prop)).mul
    cases a with
    | mk b a =>
      cases b
      · exact (ih (n+1) a).comp (measurable_fst.prodMk
          (Measurable.of_eval (fun index => (measurable_pi_apply index.succ).comp measurable_snd)))
      · exact (hw (n+1) a).comp measurable_fst

omit [MeasurableSpace X] in
lemma eval_le_one (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : State M)
    (s : X) (obs : Observations d k) : K.eval w n k j s obs ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    apply (Finset.sum_le_sum (fun a _ => mul_le_of_le_one_right' ?_)).trans_eq
      (K.transition_sum (n+1) j (obs 0))
    split
    · exact hw _ _ _
    · exact ih _ _ _

omit [MeasurableSpace X] in
lemma pathValue_le_one (hw : ∀ n j s, w n j s ≤ 1) (s : X) (obs : Observations d T) :
    K.pathValue w s obs ≤ 1 := by
  apply (Finset.sum_le_sum (fun a _ => mul_le_of_le_one_right' ?_)).trans_eq K.initial_sum
  split
  · exact hw _ _ _
  · exact K.eval_le_one w hw _ _ _ _ _

def cont (n : ℕ) : ℕ → State M → X → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
      if a.1 then w (n+1) a.2 s else cont (n+1) k a.2 s ∂stdGaussian (Vector d)

lemma measurable_cont (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (hι : Measurable ι) (n k : ℕ) (j : State M) : Measurable (K.cont w ι n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    apply Finset.measurable_sum _
    intro a _
    apply ((hK (n+1) j a).comp (by fun_prop)).mul
    rcases a with ⟨b,a⟩
    cases b
    · exact (ih (n+1) a).comp measurable_snd
    · exact (hw (n+1) a).comp measurable_snd

omit [MeasurableSpace X] in
lemma cont_le_forced_sum (hK : K.Borel) (n k : ℕ) (j : State M) (s : X) :
    K.cont w ι n k j s ≤ ∑ r ∈ Finset.range (k+1),
      MemoryPrecision.stochCont K.marginal w ι n r j s := by
  classical
  induction k generalizing n j with
  | zero => simp [cont, MemoryPrecision.stochCont]
  | succ k ih =>
    let V (a : State M) := ∑ r ∈ Finset.range (k+1),
      MemoryPrecision.stochCont K.marginal w ι (n+1) r a s
    have hwV (a : State M) : w (n+1) a s ≤ V a := by
      simpa [MemoryPrecision.stochCont] using
        (Finset.single_le_sum (fun r _ => bot_le (a := MemoryPrecision.stochCont K.marginal w ι (n+1) r a s))
          (show 0 ∈ Finset.range (k+1) by simp))
    calc
      _ ≤ ∫⁻ x, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a * V a.2
          ∂stdGaussian (Vector d) := lintegral_mono (fun x => Finset.sum_le_sum (fun a _ => by
            apply mul_le_mul' le_rfl
            split
            · exact hwV a.2
            · exact ih (n+1) a.2))
      _ = ∑ r ∈ Finset.range (k+1), MemoryPrecision.stochCont K.marginal w ι n (r+1) j s := by
        simp only [MemoryPrecision.stochCont]
        have hm (r : ℕ) : Measurable (fun x : Vector d => ∑ a,
            K.marginal (n+1) j (x,⟪ι s,x⟫) a *
              MemoryPrecision.stochCont K.marginal w ι (n+1) r a s) :=
          Finset.measurable_sum _ (fun a _ =>
            ((K.marginal_measurable hK (n+1) j a).comp (by fun_prop)).mul measurable_const)
        rw [← lintegral_finsetSum _ (fun r _ => hm r)]
        apply lintegral_congr
        intro x
        simp only [V, Finset.mul_sum, Fintype.sum_prod_type, marginal, Finset.sum_mul]
        rw [Finset.sum_comm]
        conv_lhs =>
          arg 2
          ext a
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      _ ≤ ∑ r ∈ Finset.range (k+1+1), MemoryPrecision.stochCont K.marginal w ι n r j s := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from zero_le)

end Evaluation
end Policy
end MemoryPrecision.Kernel


end

end OAI

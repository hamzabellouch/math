import OAI.Probability.InvariantIsing.Fields.VectorTerminalShift
import OAI.Probability.InvariantIsing.Fields.MarkEndpointKernel
import OAI.Probability.InvariantIsing.Magnetic.RestrictedEndpointKernel

namespace OAI

/-! The ancestor increments for the constrained terminal give its physical endpoint kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma restrictedAncestor_state {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents (n+1) b) :
    markStateKernel (vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable 0) =
    vectorGaussianTransition N (b 0) (v 0)
      (restrictedFieldRecursion S n (fun i => b (i+1)) (fun i => v (i+1)))
      (restrictedFieldRecursion_regular hN S hS n _ _
        (fun i hi => (hb.1 (i+1) (by omega)).1)).1 := by
  let := vectorTerminalAncestorKernel_markov hN (n+1) b v hb (restrictedFieldTerminal S)
    (continuous_restrictedFieldTerminal S hS).measurable (restrictedFieldTerminal_linearGrowth S hS) 0
  ext z : 1
  rw [markStateKernel_apply,vectorTerminalAncestorKernel_add hN (n+1) b v hb
    (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable
    (restrictedFieldTerminal_linearGrowth S hS) 0 (by omega)]
  simp only [zero_add,vectorTerminalBackward_one,restrictedFieldRecursion]

lemma restrictedAncestor_tail {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b) :
    markTailEndpointKernel n (vectorTerminalAncestorKernel N n b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable) =
    restrictedTailEndpointKernel hN S hS n b v (fun i hi => (hb.1 i hi).1) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have hbs : CascadeExponents n (fun i => b (i+1)) := hb.tail
    have hs : (fun i => vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
        (continuous_restrictedFieldTerminal S hS).measurable (i+1)) =
        vectorTerminalAncestorKernel N n (fun i => b (i+1)) (fun i => v (i+1))
          (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable :=
      funext fun i => vectorTerminalAncestorKernel_shift N n b v _ _ i
    rw [markTailEndpointKernel,hs,ih _ _ hbs,restrictedAncestor_state hN S hS n b v hb]
    rfl

lemma restrictedAncestor_pair {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b) (d : Fin (n+1)) :
    markPairEndpointKernel n (vectorTerminalAncestorKernel N n b v (restrictedFieldTerminal S)
      (continuous_restrictedFieldTerminal S hS).measurable) d =
    restrictedPairEndpointKernel hN S hS n b v (fun i hi => (hb.1 i hi).1) d := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · simp only [markPairEndpointKernel,restrictedPairEndpointKernel,Fin.cases_zero,
        restrictedAncestor_tail hN S hS (n+1) b v hb]
    · have hbs : CascadeExponents n (fun i => b (i+1)) := hb.tail
      have hs : (fun i => vectorTerminalAncestorKernel N (n+1) b v (restrictedFieldTerminal S)
          (continuous_restrictedFieldTerminal S hS).measurable (i+1)) =
          vectorTerminalAncestorKernel N n (fun i => b (i+1)) (fun i => v (i+1))
            (restrictedFieldTerminal S) (continuous_restrictedFieldTerminal S hS).measurable :=
        funext fun i => vectorTerminalAncestorKernel_shift N n b v _ _ i
      simp only [markPairEndpointKernel,restrictedPairEndpointKernel,Fin.cases_succ]
      rw [hs,ih _ _ hbs,restrictedAncestor_state hN S hS n b v hb]

end InvariantIsing

end

end OAI

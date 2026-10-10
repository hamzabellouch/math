import OAI.Probability.InvariantIsing.Arrays.TensorLabeledTerminal

namespace OAI

/-! Labeled terminal Gibbs replicas and the actual marked noise-tree replicas agree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma measurable_tensorLeafState_fixed {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    Measurable (tensorLeafState I degree n z) := by
  have h : Measurable (fun p : (SpinTensorIndex I degree → ℝ) ×
      NoiseLeaf (SpinTensorIndex I degree → ℝ) n => tensorLeafState I degree n p.1 p.2) := by
    induction n with
    | zero => exact measurable_fst
    | succ n ih =>
        exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)
  exact h.comp ((measurable_const (a := z)).prodMk measurable_id)

theorem tensor_labeled_noise_replica_law {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ((tensorCoordinateLaw I degree n b v) ⊗ₘ
      probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
        (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)).map
      (fun p i => labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
        (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) (p.2 i)) =
    probabilityReplicaKernel (tensorTerminalLeafLaw eig U c I degree amplitude n z)
      (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z) ∘ₘ
      tensorCascadeLaw I degree n b v := by
  let T := fun p : TensorCoordinateData I degree n =>
    labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
      (p.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : (tensorCoordinateLaw I degree n b v).map T = tensorCascadeLaw I degree n b v :=
    labeledNoiseCoordinates_law (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v i))
  have hp : MeasurePreserving T (tensorCoordinateLaw I degree n b v)
      (tensorCascadeLaw I degree n b v) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism (tensorCoordinateLaw I degree n b v)
    (tensorCascadeLaw I degree n b v)
    (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
    (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z) hT hPQ
    (ψ := fun p α => labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
      (p.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α)
  · apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n α).comp (by fun_prop)
  · have hgood := hp.quasiMeasurePreserving.tendsto_ae.eventually
      (noiseCascade_good (SpinTensorIndex I degree → ℝ) n b hb
        (fun i => tensorGaussianLaw I degree (v i)))
    filter_upwards [hgood,tensorLabeledTerminal_exp_integrable_ae hN eig U c I degree amplitude n b v hb z]
      with p hg hi
    have ht : 0 < noiseTreeTotal (SpinTensorIndex I degree → ℝ) n (T p) ∧
        noiseTreeTotal (SpinTensorIndex I degree → ℝ) n (T p) < ⊤ := by
      cases n with
      | zero => simp [noiseTreeTotal,rawTreeTotal]
      | succ n => exact hg.1
    have hbase := labeledLeafLaw_noiseMap (SpinTensorIndex I degree → ℝ) n p.1
      (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) hg ht
    let f := labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
      (p.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2)
    let H := fun w => spinTensorTerminal eig U c I degree amplitude (tensorLeafState I degree n z w)
    have hH : Measurable H := (measurable_spinTensorTerminal eig U c I degree amplitude).comp
      (measurable_tensorLeafState_fixed I degree n z)
    have hs : (fun α => H (f α)) = (fun α => spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z)) := by
      funext α
      exact congrArg (spinTensorTerminal eig U c I degree amplitude) (tensorLeafState_labeled I degree n z p α)
    have hie : Integrable (fun α => Real.exp (H (f α))) (labeledLeafLaw n p.1) := by
      convert hi using 1
      funext α
      exact congrArg Real.exp (congrFun hs α)
    have h := gibbsProbability_map_normalize (labeledLeafLaw n p.1) (f := f)
      (measurable_of_countable f) hH hie
    rw [hs,hbase] at h
    exact h

end InvariantIsing

end

end OAI

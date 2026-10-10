import OAI.Probability.InvariantIsing.Fields.VectorTerminalLabeled

namespace OAI

/-! Sampling the labeled vector terminal agrees with sampling its noise-tree representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_noise_replica_law (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : CascadeExponents n b) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1)) :
    (vectorTerminalCoordinateLaw N n b v ⊗ₘ
      probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)).map
      (fun p i => labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i)) =
    probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z) ∘ₘ
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) := by
  let T := fun p : VectorTerminalCoordinates N n => labeledNoiseJoin (Fin N → ℝ) n
    (p.1,markForestOfCoords (Fin N → ℝ) n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : (vectorTerminalCoordinateLaw N n b v).map T =
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) :=
    labeledNoiseCoordinates_law (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i))
  have hp : MeasurePreserving T (vectorTerminalCoordinateLaw N n b v)
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism (vectorTerminalCoordinateLaw N n b v) _
    (measurable_vectorLabeledTerminalLaw N n F hF z) (measurable_vectorTerminalNoiseLaw N n F hF z) hT hPQ
    (ψ := fun p α => labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2) α)
  · apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)
  · have hg := hp.quasiMeasurePreserving.tendsto_ae.eventually
      (noiseCascade_good (Fin N → ℝ) n b hb (fun i => vectorGaussianLaw N (v i)))
    filter_upwards [hg,he] with p hg hi
    have ht : 0 < noiseTreeTotal (Fin N → ℝ) n (T p) ∧ noiseTreeTotal (Fin N → ℝ) n (T p) < ⊤ := by
      cases n with
      | zero => simp [noiseTreeTotal,rawTreeTotal]
      | succ n => exact hg.1
    have hbase := labeledLeafLaw_noiseMap (Fin N → ℝ) n p.1 (markForestOfCoords (Fin N → ℝ) n p.2) hg ht
    let f := labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2)
    let H := fun w => F (vectorLeafSum N n z w)
    have hH : Measurable H := hF.comp ((measurable_vectorLeafSum N n).comp (measurable_const.prodMk measurable_id))
    have hs : (fun α => H (f α)) = (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)) := by
      funext α
      exact congrArg F (vectorLeafSum_labeled N n z p α)
    have hi' : Integrable (fun α => Real.exp (H (f α))) (labeledLeafLaw n p.1) := by
      convert hi using 1
      funext α
      exact congrArg Real.exp (congrFun hs α)
    have h := gibbsProbability_map_normalize (labeledLeafLaw n p.1) (measurable_of_countable f) hH hi'
    rw [hs,hbase] at h
    exact h

end InvariantIsing

end

end OAI

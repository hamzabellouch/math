import OAI.Probability.InvariantIsing.Cavity.CavityMarkDepthLaw
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticReplica

namespace OAI

/-! Non-atomic Gaussian coordinates identify branching in the retained
quadratic cascade. Common-level tests survive its innovation transport. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Classical Matrix

namespace InvariantIsing

lemma cavity_multivariateGaussian_nullSingleton {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (j : Fin d) (hj : 0 < S j j) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S) := by
  have hv : (S j j).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hj)
  let _ := nullSingletonClass_gaussianReal (μ := 0) hv
  constructor
  intro x
  have hp := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d)))
    hS (i := j)).map_eq
  have hz : (0 : EuclideanSpace ℝ (Fin d)) j = 0 := rfl
  rw [hz] at hp
  have hn : (gaussianReal 0 (S j j).toNNReal) {x j} = 0 := measure_singleton _
  rw [← hp, Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn
  apply measure_mono_null _ hn
  intro y hy
  exact congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) hy

theorem cavity_innovation_common_depth_integral {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (μ ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hνatom : ∀ i < n, NullSingletonClass (ν i : Measure (EuclideanSpace ℝ (Fin d))))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hgi : ∀ i s, Function.Injective (fun a => g i (s, a)))
    (hcpos : ∀ i s a, 0 < c i (s, a))
    (hν : ∀ i s, (((μ i : Measure _).withDensity
      (fun a => ENNReal.ofReal (c i (s, a) ^ b i))).map (fun a => g i (s, a))) =
        (ν i : Measure _)) (s : EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ) :
    (∫ σ, a (cavityCommonMarkDepth n (σ 0) (σ 1))
      ∂((probabilityReplicaKernel
        (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
        (measurable_noiseTiltedLeafLaw n hc (fun _ => measurable_fst.add measurable_snd) s)) ∘ₘ
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _))) =
      ∫ α, a (labeledCommonDepth n (α 0) (α 1)) ∂cascadeReplicaLaw n b := by
  let P := (probabilityReplicaKernel (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
      (measurable_noiseTiltedLeafLaw n hc (fun _ => measurable_fst.add measurable_snd) s)) ∘ₘ
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)
  let T := fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
    fun i => cavityInnovationLeaf n c g s (σ i)
  have hT : Measurable T := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_cavityInnovationLeaf n c g hc hg).comp
      (measurable_const.prodMk measurable_id)).comp (measurable_pi_apply i)
  have hF : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      a (cavityCommonMarkDepth n (σ 0) (σ 1))) :=
    by
      have hp : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
          (σ 0, σ 1)) := by fun_prop
      exact (measurable_of_countable a).comp ((cavityCommonMarkDepth_measurable n).comp hp)
  have hLaw : P.map T = markedReplicaLaw n b ν :=
    cavity_innovation_replica_law n b hb μ ν c g hc hg hcpos hν s
  change (∫ σ, a (cavityCommonMarkDepth n (σ 0) (σ 1)) ∂P) = _
  calc
    _ = ∫ σ, a (cavityCommonMarkDepth n (T σ 0) (T σ 1)) ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun σ => congrArg a
        (cavityInnovationLeaf_commonMarkDepth n c g hgi s (σ 0) (σ 1)).symm
    _ = ∫ σ, a (cavityCommonMarkDepth n (σ 0) (σ 1)) ∂markedReplicaLaw n b ν := by
      rw [← hLaw, integral_map hT.aemeasurable hF.aestronglyMeasurable]
    _ = _ := cavity_marked_common_depth_integral n b hb ν hνatom a

end InvariantIsing

end

end OAI

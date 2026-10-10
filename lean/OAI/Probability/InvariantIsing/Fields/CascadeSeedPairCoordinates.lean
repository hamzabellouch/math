import OAI.Probability.InvariantIsing.Fields.CascadeUnweightedAncestry
import OAI.Probability.InvariantIsing.Fields.SeedForestPairData
import OAI.Probability.InvariantIsing.Fields.NoiseReplicaPairData
import OAI.Probability.InvariantIsing.Arrays.ReplicaPushforward
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-! Joint seed paths and branch depth after removing the random tree coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem cascade_seed_pair_coordinates (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
      probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
        (fun p => noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) =
    ((cascadeReplicaLaw n b).prod
      (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))).map
        (seedForestPairData n ψ z) := by
  let Q := Measure.infinitePi (fun _ : ForestVertex n => (cascadeSeedLaw : Measure unitInterval))
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod Q
  let K := probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n)
  let Ψ := fun p : (LabeledTree n × (ForestVertex n → unitInterval)) × (ℕ → LabeledLeaf n) =>
    fun i => labeledNoiseLeaf unitInterval n (p.1.1,markForestOfCoords unitInterval n p.1.2) (p.2 i)
  let F := fun σ : ℕ → NoiseLeaf unitInterval n =>
    noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (σ i))
  let G := fun p : (ℕ → LabeledLeaf n) × (ForestVertex n → unitInterval) =>
    seedForestPairData n ψ z (p.1,markForestOfCoords unitInterval n p.2)
  have hF : Measurable F := (measurable_noiseReplicaPairData n).comp
    (Measurable.of_eval fun i => (measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk (measurable_pi_apply i)))
  have hG : Measurable G := (measurable_seedForestPairData n ψ hψ z).comp
    (measurable_fst.prodMk ((measurable_markForestOfCoords unitInterval n).comp measurable_snd))
  have hΨ : Measurable Ψ := by
    apply Measurable.of_eval
    intro i
    have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → unitInterval)) × LabeledLeaf n =>
        labeledNoiseLeaf unitInterval n (p.1.1,markForestOfCoords unitInterval n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left
      intro α
      exact (measurable_labeledNoiseLeaf unitInterval n α).comp (by fun_prop)
    exact hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [map_compProd_snd _ _ hF]
  change (markedReplicaLaw n b (fun _ => cascadeSeedLaw)).map F = _
  rw [← labeled_marked_replica_law n b hb (fun _ => cascadeSeedLaw),Measure.map_map hF hΨ]
  have he := independent_marks_sampling (labeledCascadeLaw n b : Measure (LabeledTree n)) Q K
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) =
    (cascadeReplicaLaw n b).prod Q at he
  have hforest : ((cascadeReplicaLaw n b).prod Q).map
      (fun p => (p.1,markForestOfCoords unitInterval n p.2)) =
      (cascadeReplicaLaw n b).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n)) := by
    change ((cascadeReplicaLaw n b).prod Q).map
      (Prod.map id (markForestOfCoords unitInterval n)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_markForestOfCoords unitInterval n),
      Measure.map_id]
    exact congrArg ((cascadeReplicaLaw n b).prod)
      (markForestOfCoords_law unitInterval n (fun _ => cascadeSeedLaw))
  rw [← hforest,Measure.map_map (measurable_seedForestPairData n ψ hψ z) (by fun_prop)]
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map (F ∘ Ψ) = ((cascadeReplicaLaw n b).prod Q).map G
  rw [← he,Measure.map_map hG (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [coordinate_unweighted_depth_ae n b hb (fun _ => cascadeSeedLaw)] with p hp
  apply Prod.ext
  · exact (noiseLeafCommonDepth_seed n ψ z z (Ψ p 0) (Ψ p 1)).trans hp
  · funext i
    exact Prod.ext (congrFun (cascadeSeedPath_labeled n ψ z p.1.1
      (markForestOfCoords unitInterval n p.1.2) (p.2 0)) i)
      (congrFun (cascadeSeedPath_labeled n ψ z p.1.1
        (markForestOfCoords unitInterval n p.1.2) (p.2 1)) i)

end InvariantIsing

end

end OAI

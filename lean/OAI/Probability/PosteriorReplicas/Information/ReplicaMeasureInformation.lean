import OAI.Probability.PosteriorReplicas.Information.RandomProjectionInformation

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma random_replica_measure_information {T W Y Z : Type*}
    [MeasurableSpace T] [MeasurableSpace W] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace W] [Nonempty W] [Fintype W] [MeasurableSingletonClass W]
    [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
    {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
    (Q : Measure ((Fin n → Y) × W)) [IsProbabilityMeasure Q]
    (q : Measure (Y × W)) [IsProbabilityMeasure q]
    (hq : ∀ i, Q.map (fun z => (z.1 i,z.2)) = q)
    {g : T × Y → Z} (hg : Measurable g) :
    (n : ℝ≥0∞)*cmi (randomSideLaw β g q) +
      (∫⁻ b, totalCorrelation (Q.fst.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation Q.fst + ENNReal.ofReal (finiteEntropy Q.snd) := by
  let R := Q.map Prod.swap
  have : IsProbabilityMeasure R := by dsimp [R]; infer_instance
  have hl (i : Fin n) : coordinateJoint R.fst R.condKernel i = q := by
    rw [coordinateJoint, coordKernel, Measure.compProd_map (measurable_pi_apply i),
      Measure.disintegrate R R.condKernel]
    change ((Q.map Prod.swap).map (fun z => (z.1,z.2 i))).map Prod.swap = q
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    exact hq i
  have h := random_replica_information_identical β R.fst R.condKernel hg q hl
  rw [Measure.disintegrate R R.condKernel] at h
  simpa only [R,Measure.fst_map_swap,Measure.snd_map_swap] using h

end PosteriorReplicas
end

end OAI

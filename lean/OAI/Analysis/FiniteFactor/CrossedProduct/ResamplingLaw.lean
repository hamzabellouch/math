import OAI.Analysis.FiniteFactor.CrossedProduct.ReferenceMixture

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

theorem sourceResampling_coordinate_compProd (I : Finset SourceCoordinate) (i : SourceCoordinate) :
    unitIntervalMeasure ⊗ₘ (if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id) =
      (unitIntervalMeasure.prod unitIntervalMeasure).map
        (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1)) := by
  by_cases hi : i ∈ I
  · simp [hi,Measure.compProd_const]
  · simp only [ite_eq_right hi,Measure.compProd_id]
    have hf : (unitIntervalMeasure.prod unitIntervalMeasure).map Prod.fst = unitIntervalMeasure :=
      measurePreserving_fst.map_eq
    conv_lhs => rw [← hf]
    rw [Measure.map_map (by fun_prop) measurable_fst]
    rfl

/-- Each replacement pattern is exactly the unrestricted source pair law. -/
theorem sourceResampling_compProd_eq_map (I : Finset SourceCoordinate) :
    sourceSamplingHaar ⊗ₘ sourceResamplingKernel I =
      sourceSamplingPairHaar.map (sourceSamplingLimitMap I) := by
  let κ := fun i : SourceCoordinate => if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id
  let : ∀ i, IsMarkovKernel (κ i) := fun i => by dsimp [κ]; split_ifs <;> infer_instance
  have hh := independentKernel_compProd (fun _ : SourceCoordinate => unitIntervalMeasure) κ
  dsimp [κ] at hh
  simp_rw [sourceResampling_coordinate_compProd] at hh
  let zip : SourceSamplingPair → (SourceCoordinate → ℝ × ℝ) := fun z i => (z.1 i,z.2 i)
  let unzip : (SourceCoordinate → ℝ × ℝ) → SourceSamplingPair := fun z => (fun i => (z i).1,fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (SourceCoordinate → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid,Measure.map_id] at hleft
  unfold sourceResamplingKernel
  rw [hleft]
  have hm (i : SourceCoordinate) : Measurable (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1)) := by
    by_cases hi : i ∈ I <;> simp only [hi,ite_true,ite_false] <;> fun_prop
  have hp : sourceSamplingPairHaar.map
      (fun z i => ((z i).1,if i ∈ I then (z i).2 else (z i).1)) =
      Measure.infinitePi (fun i : SourceCoordinate => (unitIntervalMeasure.prod unitIntervalMeasure).map
        (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1))) :=
    Measure.infinitePi_map_pi _ hm
  have hmap : Measurable (fun z : SourceCoordinate → ℝ × ℝ =>
      fun i => ((z i).1,if i ∈ I then (z i).2 else (z i).1)) :=
    Measurable.of_eval fun i => (hm i).comp (measurable_pi_apply i)
  rw [← hp,Measure.map_map hu hmap]
  rfl

end
end FiniteFactor

end OAI

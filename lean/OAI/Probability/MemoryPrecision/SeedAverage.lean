import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelEvaluation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel

lemma seed_average_bound {X Y : Type*} {Ω : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (π : Measure X) [SFinite π] (ν : Measure Y) [SFinite ν]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {f : X × (Ω × Y) → ℝ≥0∞}
    (hf : AEMeasurable f (π.prod (ρ.prod ν))) {B : ℝ≥0∞}
    (hb : ∀ᵐ ω ∂ρ, (∫⁻ z : X × Y, f (z.1,(ω,z.2)) ∂π.prod ν) ≤ B) :
    (∫⁻ z, f z ∂π.prod (ρ.prod ν)) ≤ B := by
  have hp := ((MeasurePreserving.id π).prod
      (Measure.measurePreserving_swap (μ := ν) (ν := ρ))).comp
    (measurePreserving_prodAssoc π ν ρ)
  let g : (X × Y) × Ω → ℝ≥0∞ := fun z => f (z.1.1,(z.2,z.1.2))
  have hg : AEMeasurable g ((π.prod ν).prod ρ) :=
    hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have he : (∫⁻ z, g z ∂(π.prod ν).prod ρ) = ∫⁻ z, f z ∂π.prod (ρ.prod ν) := by
    rw [← hp.map_eq]
    exact (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
  rw [← he, lintegral_prod_symm _ hg]
  exact (lintegral_mono_ae hb).trans_eq (by simp)

namespace Policy
variable {d M T : ℕ}
lemma success_le_one {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    (ε : ℝ) : Success L ρ π ε ≤ 1 := by
  have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
  unfold Success experiment
  calc
    _ ≤ ∫⁻ _z : Sphere d × (Ω × Rows d T), (1 : ℝ≥0∞) ∂π.prod (ρ.prod (RowLaw d T)) :=
      lintegral_mono (fun z => (L z.2.1).pathValue_le_one _
        ((L z.2.1).outputTest_le_one (angleTest_le_one ε)) z.1 (records z.1 z.2.2))
    _ = 1 := by simp
lemma chordSuccess_le_one {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    (ε : ℝ) : ChordSuccess L ρ π ε ≤ 1 := by
  have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
  unfold ChordSuccess experiment
  calc
    _ ≤ ∫⁻ _z : Sphere d × (Ω × Rows d T), (1 : ℝ≥0∞) ∂π.prod (ρ.prod (RowLaw d T)) :=
      lintegral_mono (fun z => (L z.2.1).pathValue_le_one _
        ((L z.2.1).outputTest_le_one (chordTest_le_one ε)) z.1 (records z.1 z.2.2))
    _ = 1 := by simp
end Policy
end MemoryPrecision.Kernel


end

end OAI

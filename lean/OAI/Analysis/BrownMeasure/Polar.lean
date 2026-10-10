import Mathlib
import OAI.Analysis.BrownMeasure.PurePoint
import OAI.Analysis.BrownMeasure.Weight

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal
namespace FiniteFactor

def sourcePolarBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ) : SourceBaseFunction where
  toFun := fun x => (sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ (-n) x):ℂ)
  measurable := Complex.measurable_ofReal.comp ((sourceCocycle_measurable θ sourceLogWeight 1).comp (by unfold coordinateRotate; fun_prop))
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x _
    exact (sourceWeightBase θ hθ).norm_le _ (fun _=>⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)

def sourcePolarFamily (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ) :=
  sourcePi θ (sourcePolarBase θ hθ n)

lemma sourcePolarFamily_selfAdjoint (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ) :
    IsSelfAdjoint (sourcePolarFamily θ hθ n) := by
  change star (sourcePi θ (sourcePolarBase θ hθ n))=sourcePi θ (sourcePolarBase θ hθ n)
  rw [sourcePi_star]
  simp only [sourceBaseStar,sourcePolarBase,Complex.star_def,Complex.conj_ofReal]

lemma sourcePolarFamily_jointPurePoint (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {ι : Type*} [Finite ι] (n : ι → ℤ) :
    PolarStructure.JointPurePoint (fun i=>sourcePolarFamily θ hθ (n i)) := by
  let r : ((SourceCoordinate → ℝ) × ℤ) → ι → ℝ := fun z i=>
    sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ (-n i) (coordinateRotate θ z.2 z.1))
  apply PolarStructure.jointPurePoint_of_countable_levels _ r
    (by
      apply Measurable.of_eval
      intro i
      exact (sourceCocycle_measurable θ sourceLogWeight 1).comp (by unfold coordinateRotate; fun_prop))
    (fun i u=>sourcePi_apply_ae θ (sourcePolarBase θ hθ (n i)) u)
    (Set.pi Set.univ fun _=>productWeightValues)
    (by
      convert Set.countable_pi (fun _ : ι=>productWeightValues_countable) using 1
      ext f
      simp)
  have hbase : ∀ᵐ z ∂sourceMeasure SourceCoordinate,finiteFloorSupport θ z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hθ.summable)
  filter_upwards [hbase] with z hz i _
  exact sourceCocycle_mem_values θ (finiteFloorSupport_rotate θ (finiteFloorSupport_rotate θ hz z.2) (-n i)) 1

lemma sourcePolarFamily_finite_atomic (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (F : Finset ℤ) :
    PolarStructure.Atomic (PolarStructure.generated (Set.range (fun n : F=>sourcePolarFamily θ hθ n))) :=
  PolarStructure.atomic_of_jointPurePoint _ (fun n=>sourcePolarFamily_selfAdjoint θ hθ n)
    (sourcePolarFamily_jointPurePoint θ hθ (fun n : F=>(n:ℤ)))
end FiniteFactor
end

end OAI

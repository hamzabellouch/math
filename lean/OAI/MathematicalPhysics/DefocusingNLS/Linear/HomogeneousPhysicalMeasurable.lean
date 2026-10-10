import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalLift
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

/-! # Physical point observations detect strong measurability in Y -/

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem stronglyMeasurable_of_homogeneousPhysical {X : Type*} [MeasurableSpace X]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : X → HomogeneousY a k)
    (hu : ∀ y : E, Measurable (fun x => homogeneousPhysicalCLM a k ha ha1 hk (u x) y)) :
    StronglyMeasurable u := by
  let := homogeneousFourierMeasure_locallyFinite a k ha1 hk
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MeasureTheory.IsSeparable (homogeneousFourierMeasure a k) := inferInstance
  let : SecondCountableTopology (HomogeneousY a k) := inferInstance
  let : MeasurableSpace (HomogeneousY a k) := borel (HomogeneousY a k)
  let : BorelSpace (HomogeneousY a k) := ⟨rfl⟩
  let J : HomogeneousY a k → ℕ → ℂ := fun f n =>
    homogeneousPhysicalCLM a k ha ha1 hk f (denseSeq E n)
  have hJ : Continuous J := continuous_pi (fun n =>
    (homogeneousPointEvaluation a k ha ha1 hk (denseSeq E n)).continuous)
  have hi : Function.Injective J := by
    intro f g h
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    apply DFunLike.coe_injective
    apply (denseRange_denseSeq E).equalizer
      (homogeneousPhysicalCLM a k ha ha1 hk f).continuous
      (homogeneousPhysicalCLM a k ha ha1 hk g).continuous
    exact h
  have hm : Measurable u := (hJ.measurableEmbedding hi).measurable_comp_iff.mp
    (Measurable.of_eval (fun n => hu (denseSeq E n)))
  exact hm.stronglyMeasurable

end DefocusingNLS

end OAI

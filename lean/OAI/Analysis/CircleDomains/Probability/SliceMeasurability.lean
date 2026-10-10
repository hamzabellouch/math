import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! Measurability from almost-everywhere continuous horizontal sections
and measurable vertical sections on a dense set. Finite simple sampling
provides the measurable approximants. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {A B : Type*} [MetricSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] [Nonempty A] [MeasurableSpace B]

theorem aestronglyMeasurable_of_dense_measurable_slices
    (μ : Measure A) (ν : Measure B) [SFinite ν] (f : A × B → ℝ)
    (D : Set A) (hD : Dense D)
    (hvertical : ∀x ∈ D, Measurable fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD.nonempty
  let q (n : ℕ) : SimpleFunc A A := SimpleFunc.approxOn id measurable_id D x₀ hx₀ n
  have hq (n : ℕ) (x : A) : q n x ∈ D := SimpleFunc.approxOn_mem measurable_id hx₀ n x
  let F (n : ℕ) (p : A × B) := f (q n p.1, p.2)
  have hF (n : ℕ) : Measurable (F n) := by
    let Q := {x : A // x ∈ (q n).range}
    let q' : A → Q := fun x => ⟨q n x, (q n).mem_range_self x⟩
    have hq' : Measurable q' := (q n).measurable.subtype_mk
    have hv : Measurable (fun p : Q × B => f (p.1.val, p.2)) := by
      apply measurable_from_prod_countable_right
      intro x
      apply hvertical x.val
      obtain ⟨a, ha⟩ := SimpleFunc.mem_range.mp x.property
      exact ha ▸ hq n a
    exact hv.comp ((hq'.comp measurable_fst).prodMk measurable_snd)
  apply aestronglyMeasurable_of_tendsto_ae (f := F) atTop
    (fun n => (hF n).stronglyMeasurable.aestronglyMeasurable)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hhorizontal] with p hp
  exact hp.tendsto p.1 |>.comp (SimpleFunc.tendsto_approxOn measurable_id hx₀ (hD p.1))

theorem aestronglyMeasurable_of_ae_continuous_slices
    [TopologicalSpace B] [BorelSpace B]
    (μ : Measure A) [μ.IsOpenPosMeasure] (ν : Measure B) [SFinite ν]
    (f : A × B → ℝ)
    (hvertical : ∀ᵐ x ∂μ, Continuous fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  apply aestronglyMeasurable_of_dense_measurable_slices μ ν f
    {x | Continuous fun y => f (x, y)} (μ.dense_of_ae hvertical)
  · intro x hx
    exact hx.measurable
  · exact hhorizontal

end CircleDomainRigidity

end

end OAI

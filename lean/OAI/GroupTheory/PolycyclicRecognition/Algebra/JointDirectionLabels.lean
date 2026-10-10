import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteLabelTransport
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Group.Compact

namespace OAI

/-! # Joint transport of direction labels in both flow times

Keeping both times as coordinates turns the horizontal flows into
measure-preserving skew products. This supplies local convergence in measure
on triples directly, including compact sets that are not product sets.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

def pairTimeMeasure : Measure (ℝ × ℝ) := volume.prod volume

instance : SigmaFinite pairTimeMeasure := by unfold pairTimeMeasure; infer_instance

instance : IsLocallyFiniteMeasure pairTimeMeasure := by unfold pairTimeMeasure; infer_instance

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def timedRightTranslation (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) (v : V) :
    C((ℝ × ℝ) × G, (ℝ × ℝ) × G) :=
  ⟨fun z => (z.1, z.2 * Exp (pick z.1 • v)), by fun_prop⟩

theorem continuous_timedRightTranslation (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) :
    Continuous (timedRightTranslation Exp hExp pick hpick) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : V × ((ℝ × ℝ) × G) =>
    (p.2.1, p.2.2 * Exp (pick p.2.1 • p.1)))
  fun_prop

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [TopologicalSpace.PseudoMetrizableSpace G] in
theorem measurePreserving_timedRightTranslation
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) (v : V) :
    MeasurePreserving (timedRightTranslation Exp hExp pick hpick v)
      (pairTimeMeasure.prod μ) (pairTimeMeasure.prod μ) := by
  exact (MeasurePreserving.id pairTimeMeasure).skew_product
    (by change Measurable (fun z : (ℝ × ℝ) × G => z.2 * Exp (pick z.1 • v)); fun_prop)
    (Eventually.of_forall (fun t => (measurePreserving_mul_right μ (Exp (pick t • v))).map_eq))

/-- A finite relation true locally on triples for nearby directions remains
true at the limiting direction. Compact carriers are built from the actual
convergent sequence and the two continuous skew products. -/
theorem finiteLabel_jointDirections_relation
    {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (label : G → L) (hlabel : Measurable label)
    (v : ℕ → V) {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀))
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K) (R : L → L → Prop)
    (hR : ∀ᶠ n in atTop, ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      R (label (z.2 * Exp (z.1.1 • v n))) (label (z.2 * Exp (z.1.2 • v n)))) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      R (label (z.2 * Exp (z.1.1 • v₀))) (label (z.2 * Exp (z.1.2 • v₀))) := by
  let F : ((ℝ × ℝ) × G) × V → (ℝ × ℝ) × G :=
    fun p => (p.1.1, p.1.2 * Exp (p.1.1.1 • p.2))
  let H : ((ℝ × ℝ) × G) × V → (ℝ × ℝ) × G :=
    fun p => (p.1.1, p.1.2 * Exp (p.1.1.2 • p.2))
  have hF : Continuous F := by fun_prop
  have hH : Continuous H := by fun_prop
  let Q := F '' (K ×ˢ insert v₀ (range v)) ∪ H '' (K ×ˢ insert v₀ (range v))
  have hQ : IsCompact Q :=
    ((hK.prod hv.isCompact_insert_range).image hF).union
      ((hK.prod hv.isCompact_insert_range).image hH)
  apply finiteLabel_relation_transport (μ := pairTimeMeasure.prod μ)
    (fun z : (ℝ × ℝ) × G => label z.2) (hlabel.comp measurable_snd)
    (fun n => timedRightTranslation Exp hExp Prod.fst continuous_fst (v n))
    (fun n => timedRightTranslation Exp hExp Prod.snd continuous_snd (v n))
    (timedRightTranslation Exp hExp Prod.fst continuous_fst v₀)
    (timedRightTranslation Exp hExp Prod.snd continuous_snd v₀)
    ((continuous_timedRightTranslation Exp hExp Prod.fst continuous_fst).continuousAt.tendsto.comp hv)
    ((continuous_timedRightTranslation Exp hExp Prod.snd continuous_snd).continuousAt.tendsto.comp hv)
    (Eventually.of_forall (fun n =>
      measurePreserving_timedRightTranslation μ Exp hExp Prod.fst continuous_fst (v n)))
    (Eventually.of_forall (fun n =>
      measurePreserving_timedRightTranslation μ Exp hExp Prod.snd continuous_snd (v n)))
    (measurePreserving_timedRightTranslation μ Exp hExp Prod.fst continuous_fst v₀)
    (measurePreserving_timedRightTranslation μ Exp hExp Prod.snd continuous_snd v₀)
    K Q hQ.measurableSet hQ.measure_ne_top _ _ R hR
  · exact Eventually.of_forall (fun n z hz => Or.inl ⟨(z, v n), ⟨hz, Or.inr ⟨n, rfl⟩⟩, rfl⟩)
  · exact Eventually.of_forall (fun n z hz => Or.inr ⟨(z, v n), ⟨hz, Or.inr ⟨n, rfl⟩⟩, rfl⟩)

end PolycyclicRecognition

end

end OAI

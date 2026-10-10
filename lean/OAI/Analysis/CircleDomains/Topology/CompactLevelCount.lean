import OAI.Analysis.CircleDomains.Sobolev.CompactPhysicalFiberCoarea
import OAI.Analysis.CircleDomains.Topology.CircleAlmostEverywhere

namespace OAI

/-! Joint measurability of actual distinct intersections with a closed
level relation. Smooth local circle branches only need continuity on the
compact chart piece being counted. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_closed_relation_path_count
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    {H : Set (X × T)} (hH : IsClosed H)
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ) :
    Measurable (fun p : K × T => pathImageCount {x | (x, p.2) ∈ H} p.1.val) := by
  let R : Set ((K × T) × PathTime) := {p | (p.1.1.val p.2, p.1.2) ∈ H}
  have hR : IsClosed R := hH.preimage
    ((continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst))
  convert measurable_timeCount hR using 1
  funext p
  rw [pathImageCount_eq_timeCount_of_injective _ p.1.val (hK _ p.1.property)]
  rfl

theorem measurable_compact_chart_circle_count
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (f : ℂ → ℝ) (hf : ContinuousOn f A) (K : Set C(PathTime, X))
    (hK : ∀ γ ∈ K, Injective γ) :
    Measurable (fun p : K × UnitAddCircle =>
      pathImageCount (π '' (A ∩ {z | (f z : UnitAddCircle) = p.2})) p.1.val) := by
  let H : Set (X × UnitAddCircle) := (fun z => (π z, (f z : UnitAddCircle))) '' A
  have hH : IsClosed H := (hA.image_of_continuousOn
    (hπ.continuousOn.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn hf))).isClosed
  have hs (t : UnitAddCircle) : {x | (x, t) ∈ H} =
      π '' (A ∩ {z | (f z : UnitAddCircle) = t}) := by
    ext x
    change (∃ z ∈ A, (π z, (f z : UnitAddCircle)) = (x, t)) ↔
      ∃ z, (z ∈ A ∧ (f z : UnitAddCircle) = t) ∧ π z = x
    simp only [Prod.mk.injEq]
    aesop
  simpa only [hs] using measurable_closed_relation_path_count hH K hK

end CircleDomainRigidity

end

end OAI

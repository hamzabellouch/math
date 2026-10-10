import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalDensity

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma conditional_packet_event_mass {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → A} (hraw : MeasurePreserving raw P ν)
    (ho : Measurable obs) {g : Position → ℝ} (hg : Continuous g) (hm : (∫ y,g y^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (S : Set Position)
    {B : Set Ω} (hB : MeasurableSet[MeasurableSpace.comap obs inferInstance] B) :
    (∫ o in B,∫ y in S,conditionalPacketDensity P raw obs g c r₀ s (obs o) y ∂volume ∂P)=
      ∫ o in B,packetMass g c r₀ s S (raw o) ∂P := by
  have hle : (MeasurableSpace.comap obs inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := ho.comap_le
  have hi := (packetMass_memLp hg hm hc hr₀ hs S ν).integrable (by norm_num)
  calc
    _ = ∫ o in B,(P[fun o => packetMass g c r₀ s S (raw o) | MeasurableSpace.comap obs inferInstance]) o ∂P :=
      integral_congr_ae (ae_restrict_of_ae (conditionalPacketDensity_annulus_eq_condExp P ν hraw ho hg hm hc hr₀ hs S))
    _ = _ := setIntegral_condExp hle (hraw.integrable_comp_of_integrable hi) hB

lemma conditional_packet_event_bound {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → A} (hraw : MeasurePreserving raw P ν)
    (ho : Measurable obs) {g : Position → ℝ} (hg : Continuous g) (hm : (∫ y,g y^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (S T : Set Position)
    (hT : MeasurableSet T)
    (hST : ∀ z y,y∈S → packetKernel g c r₀ s z y≠0 → z∈T)
    {B : Set Ω} (hB : MeasurableSet[MeasurableSpace.comap obs inferInstance] B) :
    (∫ o in B,∫ y in S,conditionalPacketDensity P raw obs g c r₀ s (obs o) y ∂volume ∂P)≤
      Real.sqrt (∫ x,(rawCount T x)^2 ∂ν)*Real.sqrt (P.real B) := by
  rw [conditional_packet_event_mass P ν hraw ho hg hm hc hr₀ hs S hB]
  have hi := (packetMass_memLp hg hm hc hr₀ hs S ν).integrable (by norm_num)
  have hX : MemLp (rawCount (n:=n) T) 2 ν := MemLp.of_bound
    (measurable_rawCount hT).aestronglyMeasurable (n:ℝ) (Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (rawCount_nonneg T x)]; exact rawCount_le_number T x))
  have hY := hX.comp_measurePreserving hraw
  calc
    _ ≤ ∫ o in B,rawCount T (raw o) ∂P := integral_mono
      (hraw.integrable_comp_of_integrable hi).integrableOn
      (hY.integrable (by norm_num)).integrableOn
      (fun o => packetMass_le_rawCount g hm hc hr₀ hs S T hST (raw o))
    _ ≤ Real.sqrt (∫ o,(rawCount T (raw o))^2 ∂P)*Real.sqrt (P.real B) :=
      exceptional_event_bound hY (Eventually.of_forall (fun o => rawCount_nonneg T (raw o))) (ho.comap_le B hB)
    _ = _ := by
      have H := integral_map hraw.measurable.aemeasurable
        (((measurable_rawCount hT).pow_const 2).aestronglyMeasurable :
          AEStronglyMeasurable (fun x : Configuration n => (rawCount T x)^2) (P.map raw))
      rw [hraw.map_eq] at H
      rw [←H]
end NeutralAtom
end

end

end OAI

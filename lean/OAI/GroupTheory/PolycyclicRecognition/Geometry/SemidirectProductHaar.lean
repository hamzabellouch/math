import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Haar measure in genuine semidirect product coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure

variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D] [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

@[instance_reducible]
def semidirectProductMeasurableSpace : MeasurableSpace (N ⋊[φ] D) :=
  borel (N ⋊[φ] D)

omit [IsTopologicalGroup N] [IsTopologicalGroup D] [MeasurableSpace N]
  [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D] in
theorem semidirectProduct_borelSpace :
    let := semidirectProductMeasurableSpace φ
    BorelSpace (N ⋊[φ] D) := by
  let := semidirectProductMeasurableSpace φ
  exact ⟨rfl⟩

variable [MeasurableSpace (N ⋊[φ] D)] [BorelSpace (N ⋊[φ] D)]
  (μN : Measure N) (μD : Measure D)

def semidirectProductMeasure : Measure (N ⋊[φ] D) :=
  Measure.map (semidirectProductHomeomorph φ).symm (μN.prod μD)

def semidirectProductRectangle (A : Set N) (B : Set D) : Set (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ) ⁻¹' (A ×ˢ B)

omit [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  [MeasurableSpace (N ⋊[φ] D)] [BorelSpace (N ⋊[φ] D)] in
theorem semidirectProductRectangle_compact {A : Set N} {B : Set D}
    (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (semidirectProductRectangle φ A B) :=
  (semidirectProductHomeomorph φ).isCompact_preimage.mpr (hA.prod hB)

omit [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  [MeasurableSpace (N ⋊[φ] D)] [BorelSpace (N ⋊[φ] D)] in
theorem semidirectProductRectangle_nonempty {A : Set N} {B : Set D}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (semidirectProductRectangle φ A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨⟨a, b⟩, ha, hb⟩

variable [SFinite μN] [SFinite μD]

omit [IsTopologicalGroup N] [IsTopologicalGroup D] [SecondCountableTopology N] [SFinite μN] in
theorem semidirectProductMeasure_rectangle {A : Set N} {B : Set D}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    semidirectProductMeasure φ μN μD (semidirectProductRectangle φ A B) = μN A * μD B := by
  let e := semidirectProductHomeomorph φ
  change (Measure.map e.symm (μN.prod μD)) (e ⁻¹' (A ×ˢ B)) = _
  rw [Measure.map_apply e.symm.measurable (e.measurable (hA.prod hB))]
  have hs : e.symm ⁻¹' (e ⁻¹' (A ×ˢ B)) = A ×ˢ B := by
    ext p
    simp only [Set.mem_preimage, e.apply_symm_apply]
  change (μN.prod μD) (e.symm ⁻¹' (e ⁻¹' (A ×ˢ B))) = _
  rw [hs, Measure.prod_prod]

variable [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant]

omit [SecondCountableTopology N] in
theorem semidirectProductMeasure_left_invariant
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) (g : N ⋊[φ] D) :
    MeasurePreserving (fun x => g * x) (semidirectProductMeasure φ μN μD)
      (semidirectProductMeasure φ μN μD) := by
  let : IsTopologicalGroup (N ⋊[φ] D) := semidirectProductTopologicalGroup φ hφ
  let e := semidirectProductHomeomorph φ
  have hp : MeasurePreserving (fun p : N × D => (g.left * φ g.right p.1, g.right * p.2))
      (μN.prod μD) (μN.prod μD) :=
    ((measurePreserving_mul_left μN g.left).comp (hpres g.right)).prod
      (measurePreserving_mul_left μD g.right)
  exact (e.symm.measurable.measurePreserving (μN.prod μD)).of_semiconj hp
    (fun _ => rfl) (continuous_const.mul continuous_id).measurable

variable [μN.IsHaarMeasure] [μD.IsHaarMeasure]

omit [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant] [SecondCountableTopology N] in
theorem semidirectProductMeasure_isHaarMeasure
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) :
    (semidirectProductMeasure φ μN μD).IsHaarMeasure :=
  { map_mul_left_eq_self := fun g =>
      (semidirectProductMeasure_left_invariant φ μN μD hφ hpres g).map_eq
    toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map (μN.prod μD)
      (semidirectProductHomeomorph φ).symm
    toIsOpenPosMeasure := (semidirectProductHomeomorph φ).symm.continuous.isOpenPosMeasure_map
      (semidirectProductHomeomorph φ).symm.surjective }

omit [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant]
  [μN.IsHaarMeasure] [μD.IsHaarMeasure] in
/-- Inversion in the cover is the factorwise inversion followed by the
measure-preserving Cartan action on the nilpotent coordinate. -/
theorem semidirectProductMeasure_isInvInvariant
    [μN.IsInvInvariant] [μD.IsInvInvariant]
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) :
    (semidirectProductMeasure φ μN μD).IsInvInvariant := by
  let : IsTopologicalGroup (N ⋊[φ] D) := semidirectProductTopologicalGroup φ hφ
  let e := semidirectProductHomeomorph φ
  have ha : MeasurePreserving (fun p : D × N => (p.1, φ p.1 p.2))
      (μD.prod μN) (μD.prod μN) := by
    apply (MeasurePreserving.id μD).skew_product (g := fun d n => φ d n)
    · exact hφ.measurable
    · exact Filter.Eventually.of_forall fun d => (hpres d).map_eq
  have hb : MeasurePreserving (fun p : N × D => (φ p.2 p.1, p.2))
      (μN.prod μD) (μN.prod μD) :=
    Measure.measurePreserving_swap.comp (ha.comp Measure.measurePreserving_swap)
  have hi : MeasurePreserving (fun p : N × D => (φ p.2⁻¹ p.1⁻¹, p.2⁻¹))
      (μN.prod μD) (μN.prod μD) :=
    hb.comp ((measurePreserving_inv μN).prod (measurePreserving_inv μD))
  have hs : MeasurePreserving Inv.inv (semidirectProductMeasure φ μN μD)
      (semidirectProductMeasure φ μN μD) :=
    (e.symm.measurable.measurePreserving (μN.prod μD)).of_semiconj hi
      (fun _ => rfl) continuous_inv.measurable
  exact ⟨hs.map_eq⟩

end PolycyclicRecognition

end

end OAI

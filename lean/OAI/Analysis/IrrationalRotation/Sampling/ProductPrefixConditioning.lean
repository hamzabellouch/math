import OAI.Analysis.IrrationalRotation.Product.ProductCoordinateSplit
import Mathlib.Probability.ConditionalProbability

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Invariant233.ProductCoordinateSplit

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem map_tail_restrict_prefix
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p]
    (s : Set ((i : Subtype p) → X i)) (hs : MeasurableSet s) :
    ((Measure.infinitePi μ).restrict ((fun x (i : Subtype p) => x i) ⁻¹' s)).map
        (fun x (i : {i // ¬p i}) => x i) =
      (Measure.infinitePi (fun i : Subtype p => μ i) s) •
        Measure.infinitePi (fun i : {i // ¬p i} => μ i) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X p
  have he := measurePreserving_split μ p
  have hpre : (fun x (i : Subtype p) => x i) ⁻¹' s =
      e ⁻¹' (s ×ˢ (Set.univ : Set ((i : {i // ¬p i}) → X i))) := by
    ext x
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  have htail : (fun x (i : {i // ¬p i}) => x i) = Prod.snd ∘ e := rfl
  rw [hpre, htail, ← Measure.map_map measurable_snd e.measurable,
    ← Measure.restrict_map e.measurable (hs.prod MeasurableSet.univ), he.map_eq,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.map_snd_prod]
  simp

theorem map_tail_cond_prefix
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p]
    (s : Set ((i : Subtype p) → X i)) (hs : MeasurableSet s)
    (hpos : Measure.infinitePi (fun i : Subtype p => μ i) s ≠ 0) :
    (ProbabilityTheory.cond (Measure.infinitePi μ)
        ((fun x (i : Subtype p) => x i) ⁻¹' s)).map
        (fun x (i : {i // ¬p i}) => x i) =
      Measure.infinitePi (fun i : {i // ¬p i} => μ i) := by
  have hprefix : MeasurePreserving (fun x (i : Subtype p) => x i)
      (Measure.infinitePi μ) (Measure.infinitePi fun i : Subtype p => μ i) :=
    measurePreserving_fst.comp (measurePreserving_split μ p)
  have hmass : Measure.infinitePi μ ((fun x (i : Subtype p) => x i) ⁻¹' s) =
      Measure.infinitePi (fun i : Subtype p => μ i) s := hprefix.measure_preimage hs.nullMeasurableSet
  rw [ProbabilityTheory.cond, Measure.map_smul, map_tail_restrict_prefix μ p s hs,
    hmass, smul_smul, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_smul]
  exact (Measurable.of_eval fun index => measurable_pi_apply index.val).aemeasurable

end Invariant233.ProductCoordinateSplit

end

end OAI

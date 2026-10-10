import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupAveragedRepresentative
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Action

namespace OAI

/-! # Exactly invariant representatives for locally compact groups

The probability equivalent to Haar measure supplies the group averaging
measure. This removes countability of the acting group from the invariant
representative construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
  (μ : Measure X) [SFinite μ]

theorem measurable_haarInvariantRepresentative (f : X → ℝ) (hf : Measurable f)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  let mG : Measure G := haar
  have hq (g : G) : QuasiMeasurePreserving (fun h => h * g) mG.toFinite mG.toFinite :=
    QuasiMeasurePreserving.mono (toFinite_absolutelyContinuous mG)
      (absolutelyContinuous_toFinite mG) (quasiMeasurePreserving_mul_right mG g)
  exact measurable_invariantRepresentative_of_groupAverage mG.toFinite hq μ f hf
    measurable_smul hi

theorem aemeasurable_haarInvariantRepresentative [SMulInvariantMeasure G X μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  let f' := hf.mk f
  have he : f =ᵐ[μ] f' := hf.ae_eq_mk
  have hfi (g : G) : (fun x => f' (g • x)) =ᵐ[μ] f' := by
    have hc := (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [he, hc, hi g] with x hx hxg hix
    exact hxg.symm.trans (hix.trans hx)
  obtain ⟨F, hF, hFe, hFi⟩ := measurable_haarInvariantRepresentative μ f' hf.measurable_mk hfi
  exact ⟨F, hF, hFe.trans he.symm, hFi⟩

end PolycyclicRecognition

end

end OAI

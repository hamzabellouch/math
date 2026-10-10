import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

/-! # Exact representatives for countable invariant actions

For a countable group, one common conull invariant set makes all the
almost-everywhere invariance identities simultaneous. Extending by zero on
its complement gives a measurable function constant on every orbit.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

variable {G X : Type*} [Group G] [Countable G]
  [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
  (μ : Measure X)

/-- A measurable almost invariant real function has an exactly invariant version. -/
theorem measurable_invariantRepresentative (f : X → ℝ) (hf : Measurable f)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  classical
  let S : Set X := {x | ∀ g : G, f (g • x) = f x}
  have hSm : MeasurableSet S := by
    have h := MeasurableSet.iInter (fun g : G =>
      measurableSet_eq_fun (hf.comp (measurable_const_smul g)) hf)
    convert h using 1
    ext x
    simp [S]
  have hSae : ∀ᵐ x ∂μ, x ∈ S := ae_all_iff.2 hi
  have hforward (g : G) (x : X) (hx : x ∈ S) : g • x ∈ S := by
    intro h
    rw [← mul_smul, hx (h * g), hx g]
  have hS (g : G) (x : X) : g • x ∈ S ↔ x ∈ S := by
    constructor
    · intro hx
      simpa only [inv_smul_smul] using hforward g⁻¹ (g • x) hx
    · exact hforward g x
  refine ⟨S.indicator f, hf.indicator hSm, ?_, ?_⟩
  · filter_upwards [hSae] with x hx
    exact indicator_of_mem hx f
  · intro g x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem ((hS g x).2 hx), indicator_of_mem hx, hx g]
    · rw [indicator_of_notMem (fun h => hx ((hS g x).1 h)), indicator_of_notMem hx]

/-- The same construction starts from any almost-everywhere measurable function. -/
theorem aemeasurable_invariantRepresentative [SMulInvariantMeasure G X μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  let f' := hf.mk f
  have he : f =ᵐ[μ] f' := hf.ae_eq_mk
  have hfi (g : G) : (fun x => f' (g • x)) =ᵐ[μ] f' := by
    have hc := (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [he, hc, hi g] with x hx hxg hix
    exact hxg.symm.trans (hix.trans hx)
  obtain ⟨F, hF, hFe, hFi⟩ := measurable_invariantRepresentative μ f' hf.measurable_mk hfi
  exact ⟨F, hF, hFe.trans he.symm, hFi⟩

end PolycyclicRecognition

end

end OAI

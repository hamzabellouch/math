import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Measurable finite products of locally finite real kernels

Only finite products of real kernels are needed for the root coordinates.
The construction uses binary kernel products and the standard finite
coordinate equivalences.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DukePrimeDegree

private theorem exists_finRealProductKernel {A : Type*} [MeasurableSpace A] (m : ℕ) :
    ∀ (κ : Fin m → Kernel A ℝ) [∀ i, IsSFiniteKernel (κ i)]
      [∀ i x, SigmaFinite (κ i x)],
    ∃ η : Kernel A (Fin m → ℝ), IsSFiniteKernel η ∧
      ∀ x, η x = Measure.pi (fun i => κ i x) := by
  induction m with
  | zero =>
      intro κ _ _
      refine ⟨Kernel.const A (Measure.dirac 0), inferInstance, ?_⟩
      intro x
      exact (Measure.pi_of_empty (fun i => κ i x) 0).symm
  | succ m ih =>
      intro κ _ _
      obtain ⟨η, hη, heq⟩ := ih (fun i => κ ((0 : Fin (m+1)).succAbove i))
      let := hη
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
      refine ⟨((κ 0).prod η).map e.symm, inferInstance, ?_⟩
      intro x
      rw [Kernel.map_apply _ e.symm.measurable, Kernel.prod_apply, heq]
      exact (MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove (fun i => κ i x) 0)).map_eq

/-- A finite product of s-finite real kernels with sigma-finite values
is again a kernel, with the expected product measure at every point. -/
theorem exists_realProductKernel {A I : Type*} [MeasurableSpace A] [Fintype I]
    (κ : I → Kernel A ℝ) [∀ i, IsSFiniteKernel (κ i)]
    [∀ i x, SigmaFinite (κ i x)] :
    ∃ η : Kernel A (I → ℝ), IsSFiniteKernel η ∧
      ∀ x, η x = Measure.pi (fun i => κ i x) := by
  let e := (Fintype.equivFin I).symm
  obtain ⟨η, hη, heq⟩ := exists_finRealProductKernel (Fintype.card I) (fun i => κ (e i))
  let := hη
  let E := MeasurableEquiv.piCongrLeft (fun _ : I => ℝ) e
  refine ⟨η.map E, inferInstance, ?_⟩
  intro x
  rw [Kernel.map_apply _ E.measurable, heq]
  exact Measure.pi_map_piCongrLeft e (fun i => κ i x)

end DukePrimeDegree

end

end OAI

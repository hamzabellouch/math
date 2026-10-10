import OAI.Analysis.KadisonKastler.ProjectionFrameCoordinates
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # Measurability of countable Hilbert coordinates

Coordinatewise measurability implies norm-Borel measurability in a countable
scalar Hilbert sum. Finite-coordinate sums give the required approximations.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace
open scoped Topology lp

noncomputable section

variable {I X : Type*} [Countable I]

/-- The scalar Hilbert coordinate space for a countable index set is separable. -/
theorem separable_scalarHilbertCoordinates : SeparableSpace ℓ²(I, ℂ) := by
  classical
  let b : HilbertBasis I ℂ ℓ²(I, ℂ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs : IsSeparable (Submodule.span ℂ (Set.range b) : Set ℓ²(I, ℂ)) :=
    (Set.countable_range b).isSeparable.span
  have hd : closure (Submodule.span ℂ (Set.range b) : Set ℓ²(I, ℂ)) = Set.univ :=
    congrArg (fun S : Submodule ℂ ℓ²(I, ℂ) => (S : Set ℓ²(I, ℂ))) b.dense_span
  exact isSeparable_univ_iff.mp (hd ▸ hs.closure)

variable [MeasurableSpace X] [MeasurableSpace ℓ²(I, ℂ)] [BorelSpace ℓ²(I, ℂ)]

/-- A field of Hilbert coordinate vectors is measurable if each scalar coordinate is. -/
theorem measurable_hilbertCoordinates (f : X → ℓ²(I, ℂ))
    (hf : ∀ i, Measurable fun x => f x i) : Measurable f := by
  classical
  let : SeparableSpace ℓ²(I, ℂ) := separable_scalarHilbertCoordinates
  let g : Finset I → X → ℓ²(I, ℂ) := fun s x => ∑ i ∈ s, lp.single 2 i (f x i)
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I)) (f := g)
  · intro s
    apply Finset.measurable_sum
    intro i _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.measurable.comp (hf i)
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single ENNReal.ofNat_ne_top (f x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Measurable columns make analysis in a variable range basis measurable. -/
theorem measurable_rangeHilbertCoordinates (P : X → H →L[ℂ] H)
    (B : ∀ x, HilbertBasis I ℂ (P x).range)
    (hB : ∀ i, Measurable fun x => (B x i : H))
    (v : ∀ x, (P x).range) (hv : Measurable fun x => (v x : H)) :
    Measurable fun x => (B x).repr (v x) := by
  apply measurable_hilbertCoordinates
  intro i
  simp only [HilbertBasis.repr_apply_apply]
  exact (hB i).inner hv

/- Measurable columns also make synthesis in a variable range basis measurable. -/
omit [MeasurableSpace ℓ²(I, ℂ)] [BorelSpace ℓ²(I, ℂ)] in
theorem measurable_rangeHilbertSynthesis (P : X → H →L[ℂ] H)
    (B : ∀ x, HilbertBasis I ℂ (P x).range)
    (hB : ∀ i, Measurable fun x => (B x i : H))
    (f : X → ℓ²(I, ℂ)) (hf : ∀ i, Measurable fun x => f x i) :
    Measurable fun x => ((B x).repr.symm (f x) : H) := by
  classical
  let g : Finset I → X → H := fun s x => ∑ i ∈ s, f x i • (B x i : H)
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I)) (f := g)
  · intro s
    exact Finset.measurable_sum _ (fun i _ => (hf i).smul (hB i))
  · rw [tendsto_pi_nhds]
    intro x
    have ht := ((P x).range.subtypeL).hasSum ((B x).hasSum_repr_symm (f x))
    change HasSum (fun i : I => f x i • (B x i : H)) ((B x).repr.symm (f x) : H)
    simpa only [map_smul, Submodule.subtypeL_apply] using ht

end

end KadisonKastler

end OAI

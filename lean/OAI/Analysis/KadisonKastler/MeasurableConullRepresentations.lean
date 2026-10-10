import OAI.Analysis.KadisonKastler.MeasurableHilbertCoordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace OAI

/-! # Measurable representatives of a separable operator-algebra field

A single measurable conull set suffices for every algebra element and vector.
Countably many dense tests are made measurable there; continuity supplies the
remaining evaluations without any uncountable intersection of conull sets.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {X A H : Type*} [MeasurableSpace X]

private theorem measurable_of_dense_parameters
    [TopologicalSpace A] [FirstCountableTopology A]
    [TopologicalSpace H] [PseudoMetrizableSpace H] [MeasurableSpace H] [BorelSpace H]
    (g : A → X → H) (hg : ∀ x, Continuous fun a => g a x)
    (d : ℕ → A) (hd : DenseRange d) (hm : ∀ n, Measurable (g (d n))) (a : A) :
    Measurable (g a) := by
  have hc : IsClosed {a | Measurable (g a)} := by
    apply IsSeqClosed.isClosed
    intro u a hu ha
    apply measurable_of_tendsto_metrizable hu
    rw [tendsto_pi_nhds]
    intro x
    exact ((hg x).tendsto a).comp ha
  exact (closure_minimal (by rintro _ ⟨n, rfl⟩; exact hm n) hc) (hd a)

variable [CStarAlgebra A] [SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

/-- An a.e. measurable representation field is strongly Borel measurable
on a single measurable conull subset, simultaneously for all evaluations. -/
theorem exists_conull_measurable_representations (μ : Measure X)
    (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a v, AEStronglyMeasurable (fun x => ρ x a v) μ) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∀ a v, Measurable fun x : s => ρ x.val a v := by
  let a : ℕ → A := denseSeq A
  let v : ℕ → H := denseSeq H
  have he : ∀ᵐ x ∂μ, ∀ n m : ℕ,
      ρ x (a n) (v m) = (hρ (a n) (v m)).mk (fun y => ρ y (a n) (v m)) x :=
    eventually_countable_forall.mpr fun n =>
      eventually_countable_forall.mpr fun m => (hρ (a n) (v m)).ae_eq_mk
  obtain ⟨s, hs, hsm, hse⟩ := he.exists_measurable_mem
  refine ⟨s, hsm, mem_ae_iff.mp hs, ?_⟩
  have htest (n m : ℕ) : Measurable fun x : s => ρ x.val (a n) (v m) := by
    have hm : Measurable fun x : s =>
        (hρ (a n) (v m)).mk (fun y => ρ y (a n) (v m)) x.val :=
      (hρ (a n) (v m)).measurable_mk.comp measurable_subtype_coe
    convert hm using 1
    funext x
    exact hse x.val x.property n m
  have ha (n : ℕ) (w : H) : Measurable fun x : s => ρ x.val (a n) w :=
    measurable_of_dense_parameters (fun (w : H) (x : s) => ρ x.val (a n) w)
      (fun x => (ρ x.val (a n)).continuous) v (denseRange_denseSeq H) (htest n) w
  intro c w
  exact measurable_of_dense_parameters (fun (c : A) (x : s) => ρ x.val c w)
    (fun x => (ContinuousLinearMap.apply ℂ H w).continuous.comp (map_continuous (ρ x.val)))
    a (denseRange_denseSeq A) (fun n => ha n w) c

/-- Extend the common conull restriction by the zero representation. This
preserves every fixed algebra element almost everywhere and is Borel everywhere. -/
theorem exists_measurable_nonunitalRepresentation_version (μ : Measure X)
    (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a v, AEStronglyMeasurable (fun x => ρ x a v) μ) :
    ∃ σ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      (∀ a v, Measurable fun x => σ x a v) ∧
      ∀ a, ∀ᵐ x ∂μ, σ x a = ρ x a := by
  classical
  obtain ⟨s, hs, hsnull, hm⟩ := exists_conull_measurable_representations μ ρ hρ
  let σ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H) := fun x => if x ∈ s then ρ x else 0
  refine ⟨σ, ?_, ?_⟩
  · intro a v
    have h := (hm a v).dite (measurable_const :
      Measurable fun _ : (sᶜ : Set X) => (0 : H)) hs
    convert h using 1
    funext x
    by_cases hx : x ∈ s <;> simp [σ, hx]
  · intro a
    filter_upwards [mem_ae_iff.mpr hsnull] with x hx
    simp only [σ, ite_eq_left hx]

end

end KadisonKastler

end OAI

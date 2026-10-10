import OAI.Analysis.CircleDomains.Probability.ScalarPairNull
import OAI.Analysis.CircleDomains.Selection.BandGraph
import OAI.Analysis.CircleDomains.Selection.FiniteTupleCompatibility

namespace OAI

/-! The scalar pair-null hypothesis of the rigidity companion gives the exact
ordered level compatibility required by the retained finite models. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

 theorem circleBandGraph_value_of_continuousAt
    {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : UnitAddCircle} (ht : (x, t) ∈ circleBandGraph U f) :
    (f x : UnitAddCircle) = t := by
  obtain ⟨⟨y, a⟩, ha, he⟩ := ht
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨b, c, s, hb, hc, _, ha⟩ := mem_intervalFiberHull_iff.mp ha
  rw [clusterGraph_fiber_eq_of_continuousAt hf hb,
    clusterGraph_fiber_eq_of_continuousAt hf hc] at ha
  have he : a = f y := by linarith
  exact congrArg (fun r : ℝ => (r : UnitAddCircle)) he.symm

 theorem scalar_pair_null_free_compatibility
    {X : Type*} [TopologicalSpace X] (U B : Set X)
    (f : X → ℝ) (hf : Continuous f) {n : ℕ} (g : Fin n → X → ℝ)
    (hg : ∀ i, Continuous (g i))
    (hpair : ∀ i, volume ((fun x => (f x, g i x)) '' B) = 0) :
    ((volume : Measure UnitAddCircle).prod
      (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure B (circleBandGraph U f)
        (fun i => circleBandGraph U (g i)) id) = 0 := by
  let E (i : Fin n) : Set (UnitAddCircle × (Fin n → UnitAddCircle)) :=
    (fun p => (p.1, p.2 i)) ⁻¹'
      ((fun x => ((f x : UnitAddCircle), (g i x : UnitAddCircle))) '' B)
  have hnull (i : Fin n) : (volume.prod (Measure.pi (fun _ : Fin n =>
      (volume : Measure UnitAddCircle)))) (E i) = 0 := by
    exact ((MeasurePreserving.id volume).prod
      (measurePreserving_eval (fun _ : Fin n => (volume : Measure UnitAddCircle)) i)).preimage_null
        (scalar_trace_pair_null_mod_one B f (g i) (hpair i))
  apply measure_mono_null (t := ⋃ i, E i) ?_ (measure_iUnion_null hnull)
  rintro p ⟨⟨x, t, θ⟩, ⟨hxB, hxf, hcomp⟩, rfl⟩
  have hxold : (x, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id := by
    by_contra hxold
    have he : connectedComponentIn
        {z | (z, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id} x = ∅ :=
      connectedComponentIn_eq_empty hxold
    change (connectedComponentIn
      {z | (z, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id} x).Nontrivial at hcomp
    exact Set.not_nontrivial_empty (he ▸ hcomp)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxold
  refine mem_iUnion.mpr ⟨i, x, hxB, ?_⟩
  exact Prod.ext (circleBandGraph_value_of_continuousAt hf.continuousAt hxf)
    (circleBandGraph_value_of_continuousAt (hg i).continuousAt hi)

 theorem scalar_seed_ordered_compatibility
    {X : Type*} [TopologicalSpace X] (U B : Set X) {m : ℕ}
    (u : Fin m → X → ℝ) (hu : ∀ i, Continuous (u i))
    (hpair : ∀ i j, i ≠ j → volume ((fun x => (u i x, u j x)) '' B) = 0)
    (j : Fin m) (n : ℕ) (labels : Fin n → Fin m) (hlt : ∀ i, labels i < j) :
    ((volume : Measure UnitAddCircle).prod
      (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure B (circleBandGraph U (u j))
        (fun i => circleBandGraph U (u i)) labels) = 0 := by
  have h := scalar_pair_null_free_compatibility U B (u j) (hu j)
    (u ∘ labels) (fun i => hu (labels i))
    (fun i => hpair j (labels i) (ne_of_gt (hlt i)))
  simpa only [freeComponentFailure, finiteLevelUnionGraph, comp_apply, id_eq] using h

 theorem scalar_family_ordered_compatibility
    {X : Type*} [TopologicalSpace X] (U B : Set X)
    (u : ℕ → X → ℝ) (hu : ∀ i, Continuous (u i))
    (hpair : ∀ i j, i ≠ j → volume ((fun x => (u i x, u j x)) '' B) = 0)
    (j n : ℕ) (labels : Fin n → ℕ) (hlt : ∀ i, labels i < j) :
    ((volume : Measure UnitAddCircle).prod
      (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure B (circleBandGraph U (u j))
        (fun i => circleBandGraph U (u i)) labels) = 0 := by
  have h := scalar_pair_null_free_compatibility U B (u j) (hu j)
    (u ∘ labels) (fun i => hu (labels i))
    (fun i => hpair j (labels i) (ne_of_gt (hlt i)))
  simpa only [freeComponentFailure, finiteLevelUnionGraph, comp_apply, id_eq] using h

end CircleDomainRigidity

end

end OAI

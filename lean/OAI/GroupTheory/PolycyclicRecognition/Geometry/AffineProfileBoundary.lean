import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # Extending affine profiles to a polytope's boundary -/

namespace PolycyclicRecognition

open Set
open scoped Topology

variable {V W Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Affineness over the interior already determines the profile over the
closed convex cell, including the contact facet. Surjectivity of height is
retained, so closure commutes with its inverse image. -/
theorem affine_profile_on_closed_cell
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (C : Set W) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hint : (interior C).Nonempty)
    (f : V → Y) (hf : Continuous f) (A : W →L[ℝ] Y) (b : Y)
    (haffine : ∀ z, q z ∈ interior C → f z = A (q z) + b) :
    ∀ z, q z ∈ C → f z = A (q z) + b := by
  have hzero : IsClosed {z : V | f z = A (q z) + b} :=
    isClosed_eq hf ((A.continuous.comp hq).add continuous_const)
  have hcl : closure (q ⁻¹' interior C) = q ⁻¹' C := by
    rw [← (q.isOpenMap_of_finiteDimensional hqsurj).preimage_closure_eq_closure_preimage hq,
      hC.closure_interior_eq_closure_of_nonempty_interior hint, hclosed.closure_eq]
  have hsub : closure (q ⁻¹' interior C) ⊆ {z : V | f z = A (q z) + b} :=
    closure_minimal haffine hzero
  rw [hcl] at hsub
  exact hsub

omit [NormedSpace ℝ V] [NormedSpace ℝ Y] in
/-- Once the linear label is fixed, evaluating at one eventually affine
point determines the limiting offset; no separate boundedness assumption
on the offsets is needed. -/
theorem affine_offset_tendsto
    (f : ℕ → C(V, Y)) (g : C(V, Y)) (hf : Filter.Tendsto f Filter.atTop (nhds g))
    (z : V) (a : Y) (b : ℕ → Y)
    (h : ∀ᶠ n in Filter.atTop, f n z = a + b n) :
    Filter.Tendsto b Filter.atTop (nhds (g z - a)) := by
  have ht := ((continuous_eval_const z).tendsto g |>.comp hf).sub_const a
  apply ht.congr'
  filter_upwards [h] with n hn
  change f n z - a = b n
  rw [hn, add_sub_cancel_left]

/-- A limiting label on expanding interior domains extends to the closed
cell. Only pointwise eventual membership is needed for the exhaustion. -/
theorem affine_profile_limit_on_closed_cell
    (q : V →ₗ[ℝ] W) (hq : Continuous q) (hqsurj : Function.Surjective q)
    (C : Set W) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hint : (interior C).Nonempty)
    (f : ℕ → C(V, Y)) (g : C(V, Y)) (hf : Filter.Tendsto f Filter.atTop (nhds g))
    (A : W →L[ℝ] Y) (b : ℕ → Y) (c : Y)
    (hb : Filter.Tendsto b Filter.atTop (nhds c))
    (haffine : ∀ z, q z ∈ interior C → ∀ᶠ n in Filter.atTop, f n z = A (q z) + b n) :
    ∀ z, q z ∈ C → g z = A (q z) + c := by
  apply affine_profile_on_closed_cell q hq hqsurj C hC hclosed hint g g.continuous A c
  intro z hz
  have hleft := (continuous_eval_const z).tendsto g |>.comp hf
  have hright := Filter.Tendsto.const_add (A (q z)) hb
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [haffine z hz] with n hn
  exact hn.symm

end PolycyclicRecognition

end OAI

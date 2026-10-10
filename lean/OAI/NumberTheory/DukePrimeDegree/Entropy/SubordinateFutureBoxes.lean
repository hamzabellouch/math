import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixWindows
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBasedMeasure

namespace OAI

/-! # Finite coordinate boxes containing complete bounded future fibers

The compact closure of the bounded intrinsic future can be transported
back to any sampled coordinate. A genuine quotient box can contain this
whole compact set, and can itself be cut down to a finite coordinate cube.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V]

theorem exists_bounded_box_containing_rebased_cube
    (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (g : G n) (s : UpperRootTransverse n × V) (t : c.Time)
    (hinj : Function.Injective (fun u => C.timeParam c hP hf g (s,u))) (R : ℝ) :
    ∃ (B : RootPrefixBox C c hP hf g) (S : ℝ), 0 < S ∧
      s ∈ B.transverse ∧ t ∈ B.time ∧ B.time ⊆ c.cube S ∧
      (c.remainingRebase hP hf t).symm '' c.cube R ⊆ B.time := by
  let E := c.remainingRebase hP hf t
  let K : Set c.Time := {t} ∪ E.symm '' c.closedCube R
  have hK : IsCompact K := isCompact_singleton.union
    ((c.closedCube_compact R).image E.symm.continuous)
  obtain ⟨B,hs,hKB⟩ := C.box_contains_compact_time c hP hf g s hinj K hK
  obtain ⟨m,hm⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ K)
    (c.remainingWindow_mono 1).directed_le
  let B' := B.shrink B.transverse (B.time ∩ c.cube (1+m)) B.transverse_open
    (B.time_open.inter (c.cube_open (1+m))) subset_rfl inter_subset_left
  refine ⟨B',1+m,by positivity,hs,?_,inter_subset_right,?_⟩
  · exact ⟨hKB (Or.inl rfl),hm (Or.inl rfl)⟩
  · intro u hu
    have huK : u ∈ K := Or.inr
      (Set.image_mono (c.cube_subset_closedCube R) hu)
    exact ⟨hKB huK,hm huK⟩

/-- Apply the compact-box construction to a bounded entire future fiber. -/
theorem exists_bounded_box_containing_futureFiber
    (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (g : G n) (s : UpperRootTransverse n × V) (t : c.Time)
    (hinj : Function.Injective (fun u => C.timeParam c hP hf g (s,u)))
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction (C.timeParam c hP hf g (s,t)) (c.word v))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))) → v ∈ c.cube R) :
    ∃ (B : RootPrefixBox C c hP hf g) (S : ℝ), 0 < S ∧
      s ∈ B.transverse ∧ t ∈ B.time ∧ B.time ⊆ c.cube S ∧
      {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (s,u))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))} ⊆ B.time := by
  obtain ⟨B,S,hS,hs,ht,hfinite,hcube⟩ :=
    C.exists_bounded_box_containing_rebased_cube c hP hf g s t hinj R
  refine ⟨B,S,hS,hs,ht,hfinite,?_⟩
  intro u hu
  have hv : c.remainingRebase hP hf t u ∈ c.cube R := by
    apply hbound
    intro k
    rw [← C.timeParam_rebased c hP hf g s t u]
    exact hu k
  apply hcube
  exact ⟨c.remainingRebase hP hf t u,hv,(c.remainingRebase hP hf t).symm_apply_apply u⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI

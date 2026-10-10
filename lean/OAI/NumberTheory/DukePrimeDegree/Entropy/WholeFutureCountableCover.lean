import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureBoxCover

namespace OAI

/-! # A countable family of boxes containing complete future fibers

The family is chosen before the sample. Bounded future fibers, transported
to the sampled coordinates, fit into one member of this fixed family.
This is the countability needed for gluing the local future laws.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]

def wholeFutureBoxFamily (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n) :
    Set (RootPrefixBox C c hP hf g) := ⋃ m : ℕ, C.longBoxFamily c hP hf g 1 m

lemma wholeFutureBoxFamily_countable (C : RootPrefixCoordinates n P V)
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (g : G n) :
    (C.wholeFutureBoxFamily c hP hf g).Countable :=
  Set.countable_iUnion fun m => C.longBoxFamily_countable c hP hf g 1 m

theorem exists_countable_box_containing_futureFiber
    (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    (s : UpperRootTransverse n × V) (t : c.Time)
    (hinj : Function.Injective (fun u => C.timeParam c hP hf g (s,u)))
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction (C.timeParam c hP hf g (s,t)) (c.word v))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))) → v ∈ c.cube R) :
    ∃ B ∈ C.wholeFutureBoxFamily c hP hf g,
      s ∈ B.transverse ∧ t ∈ B.time ∧
      ∃ j : ℕ, B.time = c.cube (1+j) ∧
      {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (s,u))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))} ⊆ B.time := by
  let E := c.remainingRebase hP hf t
  let K : Set c.Time := {t} ∪ E.symm '' c.closedCube R
  have hK : IsCompact K := isCompact_singleton.union
    ((c.closedCube_compact R).image E.symm.continuous)
  obtain ⟨j,hj⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ K)
    (c.remainingWindow_mono 1).directed_le
  obtain ⟨B,hB,hs⟩ := C.longBoxFamily_covers c hP hf g 1 j s hinj
  have htime := C.longBoxFamily_time c hP hf g 1 j B hB
  refine ⟨B, mem_iUnion.mpr ⟨j,hB⟩, hs, ?_, j, htime, ?_⟩
  · rw [htime]
    exact hj (Or.inl rfl)
  · intro u hu
    rw [htime]
    apply hj
    have hv : E u ∈ c.cube R := by
      apply hbound
      intro k
      rw [← C.timeParam_rebased c hP hf g s t u]
      exact hu k
    exact Or.inr ⟨E u,c.cube_subset_closedCube R hv,E.symm_apply_apply u⟩

end RootPrefixCoordinates
namespace RootPrefixBox

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates n P V} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_exists_countable_wholeFuture_box
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ᵐ x ∂μ, ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word v))) = Q (T^[k+m] x)) →
        v ∈ c.cube R) :
    ∀ᵐ z ∂B.coordinateMeasure μ,
      ∃ B' ∈ C.wholeFutureBoxFamily c hP hf g,
        z.1 ∈ B'.transverse ∧ z.2 ∈ B'.time ∧
        ∃ j : ℕ, B'.time = c.cube (1+j) ∧
        {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (z.1,u))) =
          Q (T^[k+m] (C.timeParam c hP hf g z))} ⊆ B'.time := by
  have hi := ae_of_ae_map measurable_fst.aemeasurable
    (B.ae_injective_slice_of_ae_free μ hfree)
  filter_upwards [hi, B.ae_coordinate_of_ambient μ hbound] with z hz hb
  exact C.exists_countable_box_containing_futureFiber c hP hf g z.1 z.2 hz T Q m R hb

end RootPrefixBox
end DukePrimeDegree

end

end OAI

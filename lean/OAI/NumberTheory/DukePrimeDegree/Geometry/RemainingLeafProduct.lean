import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalLeafInduction
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingChainExistence
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductBase

namespace OAI

/-! # The unconditional product formula for every actual remaining-subgroup leaf -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
universe u
namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_remainingLeaf_eq_intrinsicProduct
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} (hP : InitialRootPattern P)
    {D : Finset (Fin (d+1))} (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    {T : Type u} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) P T) (g : G (d+1))
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z) =
        c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree := ae_upperRoot_stabilizer_trivial d μ hA
  suffices H : ∀ m : ℕ, ∀ (P : Finset (Fin (d+1) × Fin (d+1))) (hP : InitialRootPattern P)
      (D : Finset (Fin (d+1))) (c : EliminationChain P D)
      (hf : c.finalEntries = allPositiveRoots (d+1))
      (T : Type u) [TopologicalSpace T] [SecondCountableTopology T]
      [MeasurableSpace T] [BorelSpace T]
      (C : RootPrefixCoordinates (d+1) P T) (g : G (d+1))
      (A : RootPrefixBox C c hP hf g) (R : ℝ), A.time ⊆ c.remainingWindow R 0 →
      (allPositiveRoots (d+1) \ P).card = m →
      ∀ᵐ z ∂A.coordinateMeasure μ,
        c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z) =
          c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z) by
    exact H _ P hP D c hf T C g A R hAR rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P hP D c hf T _ _ _ _ C g A R hAR hcard
    by_cases he : P = allPositiveRoots (d+1)
    · subst P
      exact RootPrefixBox.ae_completed_basedLeaf_eq_intrinsicProduct c
        (c.eq_done_of_completed hf) hP hf A R hAR μ hfree
    · have hne : allPositiveRoots (d+1) \ P ≠ ∅ := by
        intro hempty
        apply he
        exact Finset.Subset.antisymm (fun p hp => (hP p hp).1)
          (Finset.sdiff_eq_empty_iff_subset.mp hempty)
      obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image (allPositiveRoots (d+1) \ P)
        (fun r => toLex r) (Finset.nonempty_iff_ne_empty.mpr hne)
      let q : InitialRootStep (d+1) := ⟨(P,p),hP,hp,hmin⟩
      obtain ⟨c',hf'⟩ := exists_complete_chain_from_pattern (insert p P) ∅
        (initialRootPattern_insert_min hP p hp hmin) (by intro a ha; simp at ha)
      apply RootPrefixBox.ae_basedLeaf_eq_intrinsic_of_next (q := q) A R hAR c' hf' μ hfree
      intro k B hB
      have hless : (allPositiveRoots (d+1) \ insert p P).card < m := by
        rw [Finset.sdiff_insert,←hcard]
        exact Finset.card_erase_lt_of_mem hp
      apply ih _ hless (insert p P) q.next_initial ∅ c' hf' (T × ℝ)
        (C.extend hP p hp hmin) g B (1+k) ?_ rfl
      have htime := (C.extend hP p hp hmin).longBoxFamily_time
        c' q.next_initial hf' g 1 k B hB
      simpa only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero,htime]
        using (Subset.refl (c'.cube (1+k)))

end DukePrimeDegree

end

end OAI

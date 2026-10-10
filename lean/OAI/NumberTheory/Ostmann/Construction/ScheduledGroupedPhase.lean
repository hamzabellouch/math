import OAI.NumberTheory.Ostmann.Construction.ScheduledPivotPartition
import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimePhase
import OAI.NumberTheory.Ostmann.Construction.SchedulePivotUnary
import OAI.NumberTheory.Ostmann.Construction.GroupedPhaseFactorization

namespace OAI

/-! # Factoring the actual scheduled phase through the current composite pivot -/

namespace Ostmann

open scoped BigOperators Classical

/-- The arithmetic factorization uses every actual pivot constituent and
all retained slots. Its row and column conditions are proved from the schedule. -/
theorem scheduledPrimePhase_factor_pivot {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (q : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ)
    [∀ i, Fact (q i).Prime] (center : ∀ p : ℕ, ZMod p)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hfreq : ∀ i : CurrentPivotConstituent role n, ∀ s ∈ allFrequencyList n t,
      (s : ZMod (q (scheduledPartitionEquiv role n (.inl i)))) ≠ 0) :
    let e := scheduledPartitionEquiv role n
    let p := fun i => q (e i)
    let v := frequencyRoot n t
    let H := ∏ h : CopyScheduleH role n, p (.inr (.inl h))
    let Y := ∏ y : CopyScheduleY role n, p (.inr (.inr y))
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t q center =
      groupedResidueRow (fun i => p (.inl i)) (fun i => χ i.val (p (.inl i)))
        (fun i => κ i.val (p (.inl i))) (fun i => center (p (.inl i))) Y (fun _ => 1)
        (positiveIntegerPivotKey (∏ i, p (.inl i))
          (groupedPivotProduct_pos (fun i => p (.inl i))) H v) *
      retainedGroupedPhase (fun i => p (.inr i))
        (fun i => χ (copyScheduleOrigin n (e (.inr i)).val) (p (.inr i)))
        (fun i => center (p (.inr i)))
        (fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
          n t (e (.inr i)).val (p (.inr i)))
        (scheduledRetainedGraph role initialCompleteGraph pivot n) (∏ i, p (.inl i)) v := by
  dsimp only
  let e := scheduledPartitionEquiv role n
  let p := fun i => q (e i)
  let g := fun i j => copyScheduleGraph initialCompleteGraph pivot n (e i).val (e j).val
  let ν := fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (e i).val (p i)
  have hcp : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact hc (fun he => hij (e.injective he))
  have hν (i : CurrentPivotConstituent role n) :
      ν (.inl i) = κ i.val (p (.inl i)) *
        χ (copyScheduleOrigin n (e (.inl i)).val) (p (.inl i))
          ((frequencyRoot n t : ℤ) : ZMod (p (.inl i))) ^ (- (1 : ℤ)) := by
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (copySchedulePositive n i.val) (p (.inl i)) = _
    rw [copyScheduleUnary_pivot role χ κ pivot hpivot i.val n i.property
      (p (.inl i)) n le_rfl t (hfreq i)]
    simp only [regularUnary, e, scheduledPartitionEquiv_pivot, copyScheduleOrigin_positive]
  have hrow (i : CurrentPivotConstituent role n) (j) (hji : j ≠ .inl i) : g (.inl i) j = 1 := by
    apply scheduledRegularRow_pivot role pivot hpivot i.val n i.property n le_rfl
    · exact (e j).property
    · intro he
      have he' : e j = e (.inl i) := Subtype.ext he
      exact hji (e.injective he')
  have hself (i : CurrentPivotConstituent role n) : g (.inl i) (.inl i) = 0 :=
    copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _
  have hcolumn (i : CopyScheduleH role n ⊕ CopyScheduleY role n)
      (k : CurrentPivotConstituent role n) :
      g (.inr i) (.inl k) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none := by
    dsimp only [g, e]
    rw [scheduledPartitionEquiv_rest, scheduledPartitionEquiv_pivot]
    exact (scheduledRetainedGraph_pivot_column role pivot hpivot n k.val k.property i).symm
  have hrest (i j : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      g (.inr i) (.inr j) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) (some j) := by
    cases i <;> cases j <;> rfl
  have he := directedPrimePhase_factor_grouped p
    (fun i => χ (copyScheduleOrigin n (e i).val) (p i))
    (fun i => center (p i)) ν g (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun i => κ i.val (p (.inl i))) (fun _ => 1)
    (∏ h : CopyScheduleH role n, p (.inr (.inl h)))
    (∏ y : CopyScheduleY role n, p (.inr (.inr y))) (frequencyRoot n t)
    hcp (by exact Fintype.prod_sum_type _) (fun i => hfreq i _ (frequencyRoot_mem_allFrequencyList n t))
    hν hself hrow hcolumn hrest
  have hreindex := directedPrimePhase_equiv e q
    (fun i => χ (copyScheduleOrigin n i.val) (q i)) (fun i => center (q i))
    (fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t i.val (q i))
    (fun i j => copyScheduleGraph initialCompleteGraph pivot n i.val j.val) (frequencyRoot n t)
  unfold scheduledPrimePhase
  rw [← hreindex]
  simpa only [e, p, g, ν, scheduledPartitionEquiv_pivot, copyScheduleOrigin_positive] using he

end Ostmann

end OAI

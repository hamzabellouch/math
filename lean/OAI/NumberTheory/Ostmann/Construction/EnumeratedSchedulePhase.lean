import OAI.NumberTheory.Ostmann.Construction.ScheduledGroupedPhase

namespace OAI

/-! # The actual pivot phase in the enumeration used by the harmonic prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def enumeratedPartitionEquiv {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) :
    Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) ≃
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} :=
  (Equiv.sumCongr e (Equiv.refl _)).trans (scheduledPartitionEquiv role n)

@[simp] theorem enumeratedPartitionEquiv_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (i : Fin r) :
    (enumeratedPartitionEquiv role n r e (.inl i)).val = copySchedulePositive n (e i).val := rfl

@[simp] theorem enumeratedPartitionEquiv_rest {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (enumeratedPartitionEquiv role n r e (.inr i)).val = Sum.elim Subtype.val Subtype.val i := by
  cases i <;> rfl

theorem scheduledPrimePhase_factor_enumerated {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e₀ : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (q : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ)
    [∀ i, Fact (q i).Prime] (center : ∀ p : ℕ, ZMod p)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hfreq : ∀ i : Fin r, ∀ s ∈ allFrequencyList n t,
      (s : ZMod (q (enumeratedPartitionEquiv role n r e₀ (.inl i)))) ≠ 0) :
    let e := enumeratedPartitionEquiv role n r e₀
    let p := fun i => q (e i)
    let v := frequencyRoot n t
    let H := ∏ h : CopyScheduleH role n, p (.inr (.inl h))
    let Y := ∏ y : CopyScheduleY role n, p (.inr (.inr y))
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t q center =
      groupedResidueRow (fun i => p (.inl i)) (fun i => χ (e₀ i).val (p (.inl i)))
        (fun i => κ (e₀ i).val (p (.inl i))) (fun i => center (p (.inl i))) Y (fun _ => 1)
        (positiveIntegerPivotKey (∏ i, p (.inl i))
          (groupedPivotProduct_pos (fun i => p (.inl i))) H v) *
      retainedPrimePhase (fun h => p (.inr (.inl h))) (fun y => p (.inr (.inr y))) center
        (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
        (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
          n t h.val (p (.inr (.inl h))))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
          n t y.val (p (.inr (.inr y)))) (∏ i, p (.inl i)) v := by
  dsimp only
  let e := enumeratedPartitionEquiv role n r e₀
  let p := fun i => q (e i)
  let g := fun i j => copyScheduleGraph initialCompleteGraph pivot n (e i).val (e j).val
  let ν := fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (e i).val (p i)
  have hcp : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact hc (fun he => hij (e.injective he))
  have hν (i : Fin r) : ν (.inl i) = κ (e₀ i).val (p (.inl i)) *
      χ (copyScheduleOrigin n (e (.inl i)).val) (p (.inl i))
        ((frequencyRoot n t : ℤ) : ZMod (p (.inl i))) ^ (-(1 : ℤ)) := by
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (copySchedulePositive n (e₀ i).val) (p (.inl i)) = _
    rw [copyScheduleUnary_pivot role χ κ pivot hpivot (e₀ i).val n (e₀ i).property
      (p (.inl i)) n le_rfl t (hfreq i)]
    simp only [regularUnary, e, enumeratedPartitionEquiv_pivot, copyScheduleOrigin_positive]
  have hrow (i : Fin r) (j) (hji : j ≠ .inl i) : g (.inl i) j = 1 := by
    apply scheduledRegularRow_pivot role pivot hpivot (e₀ i).val n (e₀ i).property n le_rfl
    · exact (e j).property
    · intro he
      exact hji (e.injective (Subtype.ext he))
  have hself (i : Fin r) : g (.inl i) (.inl i) = 0 :=
    copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _
  have hcolumn (i : CopyScheduleH role n ⊕ CopyScheduleY role n) (k : Fin r) :
      g (.inr i) (.inl k) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none := by
    dsimp only [g, e]
    rw [enumeratedPartitionEquiv_rest, enumeratedPartitionEquiv_pivot]
    exact (scheduledRetainedGraph_pivot_column role pivot hpivot n (e₀ k).val (e₀ k).property i).symm
  have hrest (i j : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      g (.inr i) (.inr j) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) (some j) := by
    cases i <;> cases j <;> rfl
  have he := directedPrimePhase_factor_grouped p
    (fun i => χ (copyScheduleOrigin n (e i).val) (p i))
    (fun i => center (p i)) ν g (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun i => κ (e₀ i).val (p (.inl i))) (fun _ => 1)
    (∏ h : CopyScheduleH role n, p (.inr (.inl h)))
    (∏ y : CopyScheduleY role n, p (.inr (.inr y))) (frequencyRoot n t)
    hcp (Fintype.prod_sum_type _) (fun i => hfreq i _ (frequencyRoot_mem_allFrequencyList n t))
    hν hself hrow hcolumn hrest
  have hreindex := directedPrimePhase_equiv e q
    (fun i => χ (copyScheduleOrigin n i.val) (q i)) (fun i => center (q i))
    (fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t i.val (q i))
    (fun i j => copyScheduleGraph initialCompleteGraph pivot n i.val j.val) (frequencyRoot n t)
  unfold scheduledPrimePhase
  rw [← hreindex]
  rw [retainedGroupedPhase_split (fun i => p (.inr i))
    (fun i => χ (copyScheduleOrigin n (e (.inr i)).val)) center] at he
  simpa only [e, p, g, ν, enumeratedPartitionEquiv_pivot, enumeratedPartitionEquiv_rest,
    copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr] using he

end Ostmann

end OAI

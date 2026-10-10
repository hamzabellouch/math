import OAI.NumberTheory.Ostmann.Construction.EnumeratedSchedulePhase
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeTupleResidueRow

namespace OAI

/-! # The actual current phase under independent pivot/H/Y assignments -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledInputLabels {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ) :
    {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ :=
  fun i => Sum.elim P (Sum.elim L U) ((enumeratedPartitionEquiv role n r e).symm i)

theorem scheduledInputPrimeFact {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [hp : ∀ i, Fact (P i).Prime] [hl : ∀ i, Fact (L i).Prime] [hu : ∀ i, Fact (U i).Prime] :
    ∀ i, Fact (scheduledInputLabels role n r e P L U i).Prime := by
  intro i
  unfold scheduledInputLabels
  rcases (enumeratedPartitionEquiv role n r e).symm i with p | h | y
  · exact hp p
  · exact hl h
  · exact hu y

@[simp] theorem scheduledInputLabels_apply {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    (i : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledInputLabels role n r e P L U (enumeratedPartitionEquiv role n r e i) =
      Sum.elim P (Sum.elim L U) i := by
  simp only [scheduledInputLabels, Equiv.symm_apply_apply]

/-- The actual factorization is in the very same finite enumeration as the
original harmonic pivot prior and its residue-row transfer. -/
theorem scheduledInputPhase_factor {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ i, Fact (P i).Prime] [∀ i, Fact (L i).Prime] [∀ i, Fact (U i).Prime]
    (center : ∀ p : ℕ, ZMod p)
    (hc : Pairwise (fun i j => (Sum.elim P (Sum.elim L U) i).Coprime
      (Sum.elim P (Sum.elim L U) j)))
    (hfreq : ∀ i, ∀ s ∈ allFrequencyList n t, (s : ZMod (P i)) ≠ 0) :
    letI := scheduledInputPrimeFact role n r e P L U
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
      (scheduledInputLabels role n r e P L U) center =
      groupedResidueRow P (fun i => χ (e i).val (P i)) (fun i => κ (e i).val (P i))
        (fun i => center (P i)) (∏ y, U y) (fun _ => 1)
        (positiveIntegerPivotKey (∏ i, P i) (groupedPivotProduct_pos P)
          (∏ h, L h) (frequencyRoot n t)) *
      retainedPrimePhase L U center (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val (L h))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val (U y))
        (∏ i, P i) (frequencyRoot n t) := by
  let := scheduledInputPrimeFact role n r e P L U
  let E := enumeratedPartitionEquiv role n r e
  let p : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℕ := Sum.elim P (Sum.elim L U)
  let hp : ∀ i, Fact (p i).Prime := by
    intro i
    rcases i with i | h | y
    · exact inferInstanceAs (Fact (P i).Prime)
    · exact inferInstanceAs (Fact (L h).Prime)
    · exact inferInstanceAs (Fact (U y).Prime)
  let hpR : ∀ i, Fact (p (.inr i)).Prime := fun i => hp (.inr i)
  let ν := fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (E i).val (p i)
  let g := fun i j => copyScheduleGraph initialCompleteGraph pivot n (E i).val (E j).val
  have hν (i : Fin r) : ν (.inl i) = κ (e i).val (p (.inl i)) *
      χ (copyScheduleOrigin n (E (.inl i)).val) (p (.inl i))
        ((frequencyRoot n t : ℤ) : ZMod (p (.inl i))) ^ (-(1 : ℤ)) := by
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (copySchedulePositive n (e i).val) (P i) = _
    rw [copyScheduleUnary_pivot role χ κ pivot hpivot (e i).val n (e i).property
      (P i) n le_rfl t (hfreq i)]
    simp only [regularUnary, E, enumeratedPartitionEquiv_pivot, copyScheduleOrigin_positive, p, Sum.elim_inl]
    rfl
  have hrow (i : Fin r) (j) (hji : j ≠ .inl i) : g (.inl i) j = 1 := by
    apply scheduledRegularRow_pivot role pivot hpivot (e i).val n (e i).property n le_rfl
    · exact (E j).property
    · intro he
      exact hji (E.injective (Subtype.ext he))
  have hself (i : Fin r) : g (.inl i) (.inl i) = 0 :=
    copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _
  have hcolumn (i : CopyScheduleH role n ⊕ CopyScheduleY role n) (k : Fin r) :
      g (.inr i) (.inl k) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none := by
    dsimp only [g, E]
    rw [enumeratedPartitionEquiv_rest, enumeratedPartitionEquiv_pivot]
    exact (scheduledRetainedGraph_pivot_column role pivot hpivot n (e k).val (e k).property i).symm
  have hrest (i j : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      g (.inr i) (.inr j) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) (some j) := by
    cases i <;> cases j <;> rfl
  have he := directedPrimePhase_factor_grouped p
    (fun i => χ (copyScheduleOrigin n (E i).val) (p i))
    (fun i => center (p i)) ν g (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun i => κ (e i).val (P i)) (fun _ => 1) (∏ h, L h) (∏ y, U y) (frequencyRoot n t)
    hc (by simp only [p, Sum.elim_inr, Fintype.prod_sum_type, Sum.elim_inl])
    (fun i => hfreq i _ (frequencyRoot_mem_allFrequencyList n t)) hν hself hrow hcolumn hrest
  have hr := directedPrimePhase_equiv E.symm p
    (fun i => χ (copyScheduleOrigin n (E i).val) (p i)) (fun i => center (p i)) ν g
    (frequencyRoot n t)
  have hχ : (fun i => χ (copyScheduleOrigin n (E (E.symm i)).val) (p (E.symm i))) =
      (fun i => χ (copyScheduleOrigin n i.val) (p (E.symm i))) := by
    funext i
    rw [E.apply_symm_apply]
  have hu : (fun i => ν (E.symm i)) =
      (fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n t i.val (p (E.symm i))) := by
    funext i
    dsimp only [ν]
    rw [E.apply_symm_apply]
  have hg : (fun i j => g (E.symm i) (E.symm j)) =
      (fun i j => copyScheduleGraph initialCompleteGraph pivot n i.val j.val) := by
    funext i j
    dsimp only [g]
    rw [E.apply_symm_apply, E.apply_symm_apply]
  rw [hχ, hu, hg] at hr
  have hr' : scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (scheduledInputLabels role n r e P L U) center =
      directedPrimePhase p (fun i => χ (copyScheduleOrigin n (E i).val) (p i))
        (fun i => center (p i)) ν g (frequencyRoot n t) := hr
  rw [hr']
  rw [retainedGroupedPhase_split (fun i => p (.inr i))
    (fun i => χ (copyScheduleOrigin n (E (.inr i)).val)) center] at he
  simpa only [E, p, ν, g, enumeratedPartitionEquiv_pivot, enumeratedPartitionEquiv_rest,
    copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr] using he

/-- Pairwise support on the retained branch and coprimality with the total
pivot already imply all the constituent-level cross checks. -/
theorem pivot_retained_pairwise {r : ℕ} {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Fin r → ℕ) (L : H → ℕ) (U : Y → ℕ)
    (hP : Pairwise (fun i j => (P i).Coprime (P j)))
    (hLU : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hM : (∏ i, P i).Coprime ((∏ h, L h) * ∏ y, U y)) :
    Pairwise (fun i j => (Sum.elim P (Sum.elim L U) i).Coprime
      (Sum.elim P (Sum.elim L U) j)) := by
  have hM' : (∏ i, P i).Coprime (∏ j : H ⊕ Y, Sum.elim L U j) := by
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hM
  have hcross (i : Fin r) (j : H ⊕ Y) : (P i).Coprime (Sum.elim L U j) :=
    Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_fintype_prod_left_iff.mp hM' i) j
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact hP (fun he => hij (congrArg Sum.inl he))
  · exact hcross i j
  · exact (hcross j i).symm
  · exact hLU (fun he => hij (congrArg Sum.inr he))

end Ostmann

end OAI

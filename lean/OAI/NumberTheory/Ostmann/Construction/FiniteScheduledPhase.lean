import OAI.NumberTheory.Ostmann.Construction.FinitePivotSchedule

namespace OAI

/-! # Current phase identities with only the finitely used pivot roles -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduledInputPhase_factor_finite {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
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
    rw [copyScheduleUnary_pivot_finite role χ κ pivot (e i).val n (e i).property
      (P i) n le_rfl hpivot t (hfreq i)]
    simp only [regularUnary, E, enumeratedPartitionEquiv_pivot, copyScheduleOrigin_positive, p, Sum.elim_inl]
    rfl
  have hrow (i : Fin r) (j) (hji : j ≠ .inl i) : g (.inl i) j = 1 := by
    apply scheduledRegularRow_pivot_finite role pivot (e i).val n (e i).property n le_rfl hpivot
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
    exact (scheduledRetainedGraph_pivot_column_finite role pivot n (hpivot n le_rfl) (e k).val (e k).property i).symm
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

theorem sampledScheduledPhase_factor_finite {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P) (hx : Function.Injective x)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p)
    (hLU : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hM : (∏ i, (x i : ℕ)).Coprime ((∏ h, L h) * ∏ y, U y))
    (hfreq : ∀ i, ∀ s ∈ allFrequencyList n t, (s : ZMod (x i : ℕ)) ≠ 0) :
    sampledScheduledPhase role χ κ pivot n r e t P hP x L U center =
      primeTupleResidueRow P hP (fun i => χ (e i).val)
        (fun i p => κ (e i).val p) center (∏ y, U y) (fun _ => 1) x
        (primeTuplePivotKey P hP x (∏ h, L h) (frequencyRoot n t)) *
      retainedPrimePhase L U center (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val (L h))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val (U y))
        (∏ i, (x i : ℕ)) (frequencyRoot n t) := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  let := scheduledInputPrimeFact role n r e (fun i => (x i : ℕ)) L U
  have hcp : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hx (Subtype.ext he))
  have h := scheduledInputPhase_factor_finite role χ κ pivot n r hpivot e t
    (fun i => (x i : ℕ)) L U center (pivot_retained_pairwise _ L U hcp hLU hM) hfreq
  simpa only [sampledScheduledPhase, primeTupleResidueRow, primeTuplePivotKey] using h

theorem scheduledCurrentAmplitude_eq_grouped_finite {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (hS : ∀ x ∈ S, Function.Injective x)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hsupport : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      (∏ i, (x i : ℕ)).Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ =
    groupedDirectedAmplitude P hP Q S (fun i => χ (e i).val)
      (fun i p => κ (e i).val p) (fun _ => 1) L U center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph role initialCompleteGraph pivot n)
      (fun _z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) h.val (L a h))
      (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ := by
  unfold scheduledCurrentAmplitude groupedDirectedAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hW : W z (∏ i, (x i : ℕ)) a = 0
  · simp only [hW, retainedWeightedCoefficient, zero_mul, mul_zero]
  obtain ⟨hc, hM, hf⟩ := hsupport z x hx a hW
  rw [sampledScheduledPhase_factor_finite role χ κ pivot n r hpivot e (hist a) P hP x
    (hS x hx) (L a) (U z) center hc hM hf]
  unfold retainedWeightedCoefficient
  ring

end Ostmann

end OAI

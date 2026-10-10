import OAI.NumberTheory.Ostmann.Construction.ScheduledCurrentAmplitude

namespace OAI

/-! # Repeated prime constituents of the current pivot vanish identically -/

namespace Ostmann

open scoped BigOperators Classical

theorem directedPrimePhase_eq_zero_of_edge {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (center : ∀ i, ZMod (p i)) (ν : I → ℂ) (g : I → I → ℤ) (s : ℤ)
    (i j : I) (hg : g i j = 1) (hp : p j = p i) :
    directedPrimePhase p χ center ν g s = 0 := by
  unfold directedPrimePhase
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hrow : (∏ k, χ i (p k : ZMod (p i)) ^ g i k) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hg, zpow_one, hp, ZMod.natCast_self]
    exact (χ i).map_zero' (Fact.out : (p i).Prime).ne_one
  rw [hrow, mul_zero]

/-- Restricting the current pivot tuple to distinct primes loses no amplitude:
its regular row already kills every repeated tuple. -/
theorem sampledScheduledPhase_eq_zero_of_repeat {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (i j : Fin r) (hij : i ≠ j) (hrep : x i = x j) :
    sampledScheduledPhase role χ κ pivot n r e t P hP x L U center = 0 := by
  let : ∀ k, Fact (x k : ℕ).Prime := fun k => ⟨hP _ (x k).property⟩
  let := scheduledInputPrimeFact role n r e (fun k => (x k : ℕ)) L U
  let E := enumeratedPartitionEquiv role n r e
  unfold sampledScheduledPhase scheduledPrimePhase
  apply directedPrimePhase_eq_zero_of_edge _ _ _ _ _ _ (E (.inl i)) (E (.inl j))
  · apply scheduledRegularRow_pivot role pivot hpivot (e i).val n (e i).property n le_rfl
    · exact (E (.inl j)).property
    · intro he
      apply hij
      have hEq : E (.inl j) = E (.inl i) := Subtype.ext he
      exact (Sum.inl.inj (E.injective hEq)).symm
  · simpa only [E, scheduledInputLabels_apply, Sum.elim_inl] using
      (congrArg (fun q : P => (q : ℕ)) hrep).symm

theorem sampledScheduledPhase_eq_zero_of_not_injective {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (hx : ¬ Function.Injective x) :
    sampledScheduledPhase role χ κ pivot n r e t P hP x L U center = 0 := by
  obtain ⟨i, j, he, hij⟩ := Function.not_injective_iff.mp hx
  exact sampledScheduledPhase_eq_zero_of_repeat role χ κ pivot hpivot n r e t P hP x L U center i j hij he

/-- The tuple set required by the factorial Cauchy bound is obtained exactly;
there is no repeated-prime loss at a pivot elimination. -/
theorem scheduledCurrentAmplitude_restrict_injective {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q Finset.univ L U center W μ =
      scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q
        (Finset.univ.filter Function.Injective) L U center W μ := by
  unfold scheduledCurrentAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hi : ¬ Function.Injective x := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hz : (∑ a, W z (∏ i, (x i : ℕ)) a *
      sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [sampledScheduledPhase_eq_zero_of_not_injective role χ κ pivot hpivot
      n r e (hist a) P hP x (L a) (U z) center hi, mul_zero]
  rw [hz, mul_zero]

end Ostmann

end OAI

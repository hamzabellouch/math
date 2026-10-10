import OAI.NumberTheory.Ostmann.Construction.ConstituentOriginalAmplitude
import OAI.NumberTheory.Ostmann.Construction.PrimeGuardedAmplitude
import OAI.NumberTheory.Ostmann.Construction.ConstituentTransferWeight

namespace OAI

/-! # The original-prior expectation with every constituent-prime guard -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentPrimeGuardedAmplitude {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) : ℂ :=
  ∑ q : SurvivingConstituent role size n → P,
    ((∏ i, scheduledRolePrior (fun i : Σ a, Fin (size a) => role i.1)
      (fun j => primeSubsetPrior P (Q j)) n i (q i) : ℝ) : ℂ) *
    ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
      (hist d) * (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
        scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
          χ κ pivot n (hist d) P hP q center else 0)

/-- This identifies the full original-prior expectation, including its actual
phase and every history guard, with the amplitude in the proved arithmetic step. -/
theorem constituentPrimeGuardedAmplitude_eq_current {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      primeGuardedCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩)
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  have hF := constituent_weighted_prior_fubini role size n p hp hu P
    (scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) n)
    childBound pivotBound ranges leaf hist
    (fun q d => if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase ρ χ κ pivot n (hist d) P hP q center else 0)
  change constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center = _ at hF
  refine hF.trans ?_
  simp only [scheduledRolePrior, enumeratedPartitionEquiv_pivot,
    enumeratedPartitionEquiv_rest, copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr]
  unfold primeGuardedCurrentAmplitude constituentCurrentWeight productPrior
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [ρ]
  have hsum (j : Fin (size p) ⊕ (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n)) :
      ((Sum.elim x (Sum.elim l u) j : P) : ℕ) =
        Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) j := by
    rcases j with k | h | y <;> rfl
  have hg : (Pairwise (fun i j =>
      ((scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
        n (size p) (pivotConstituentEquiv role size n p hp hu) u x l i : P) : ℕ).Coprime
      ((scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
        n (size p) (pivotConstituentEquiv role size n p hp hu) u x l j : P) : ℕ))) ↔
      Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) i).Coprime
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) j)) := by
    have hh := scheduledPartitionAssignment_pairwise_iff (fun i : Σ a, Fin (size a) => role i.1)
      n (size p) (pivotConstituentEquiv role size n p hp hu) (fun q : P => (q : ℕ)) u x l
    simpa only [hsum] using hh
  rw [scheduledSamplePhase_partition]
  have hq (k) : Q (pivotConstituentEquiv role size n p hp hu k).val = Q ⟨p, k⟩ := rfl
  simp_rw [hq]
  split_ifs with hA hB hB
  · ring
  · exact False.elim (hB (hg.mp hA))
  · exact False.elim (hA (hg.mpr hB))
  · ring

/-- The fully guarded original expectation is exactly the amplitude to which
the proved arithmetic transfer applies. All prime-support predicates are retained. -/
theorem constituentPrimeGuardedAmplitude_eq_transfer {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      scheduledCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩) (Finset.univ.filter Function.Injective)
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  have he := constituentPrimeGuardedAmplitude_eq_current role size χ κ pivot n p hp hu
    P hP Q childBound pivotBound ranges leaf hist center
  refine he.trans ?_
  apply primeGuardedCurrentAmplitude_eq_restricted
  intro u x a hw
  exact constituentCurrentWeight_pivot_coprime role size n p hp P Q childBound pivotBound ranges
    leaf hist u (∏ i, (x i : ℕ)) a hw

end Ostmann

end OAI

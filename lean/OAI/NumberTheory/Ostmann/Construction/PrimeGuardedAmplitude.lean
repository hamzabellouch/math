import OAI.NumberTheory.Ostmann.Construction.ScheduledCurrentAmplitude
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleSupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledPriorFubini

namespace OAI

/-! # The full constituent-prime guard in arithmetic amplitude coordinates -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledPartitionAssignment_pairwise_iff {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (f : A → ℕ) (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    Pairwise (fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
      (f (scheduledPartitionAssignment role n r e u x l j))) ↔
      Pairwise (fun i j => (f (Sum.elim x (Sum.elim l u) i)).Coprime
        (f (Sum.elim x (Sum.elim l u) j))) := by
  have he : Pairwise (fun i j =>
      (f (scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e i))).Coprime
      (f (scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e j)))) ↔
      Pairwise (fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
        (f (scheduledPartitionAssignment role n r e u x l j))) :=
    (enumeratedPartitionEquiv role n r e).bijective.pairwise_comp_iff
      (r := fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
        (f (scheduledPartitionAssignment role n r e u x l j)))
  simpa only [scheduledPartitionAssignment_apply] using he.symm

noncomputable def primeGuardedCurrentAmplitude {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x : Fin r → P,
    (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, if Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
          (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) then
      W z (∏ i, (x i : ℕ)) a *
        sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center
    else 0

/-- The full prime guard separates exactly into an injective pivot tuple and
the retained branch guard. Pivot coprimality is supplied by the inherited
coefficient, so it is not added as a new hypothesis on the main theorem. -/
theorem primeGuardedCurrentAmplitude_eq_restricted {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hM : ∀ z (x : Fin r → P) a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      (∏ i, (x i : ℕ)).Coprime ((∏ h, L a h) * ∏ y, U z y)) :
    primeGuardedCurrentAmplitude role χ κ pivot n r e hist P hP Q L U center W μ =
      scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q
        (Finset.univ.filter Function.Injective) L U center
        (fun z M a => if Pairwise (fun i j =>
          (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) then W z M a else 0) μ := by
  unfold primeGuardedCurrentAmplitude scheduledCurrentAmplitude
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Function.Injective x
  · simp only [hx, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hw : W z (∏ i, (x i : ℕ)) a = 0
    · simp only [hw, zero_mul, ite_self]
    · by_cases hb : Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j))
      · have hf := (pivot_retained_pairwise_iff P hP x (L a) (U z)).mpr ⟨hx, hb, hM z x a hw⟩
        simp only [hf, hb, ite_true]
      · have hf : ¬ Pairwise (fun i j =>
            (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
              (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) :=
          fun h => hb ((pivot_retained_pairwise_iff P hP x (L a) (U z)).mp h).2.1
        simp only [hf, hb, ite_false, zero_mul]
  · simp only [hx, ite_false]
    have hz : (∑ a, if Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
          (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) then
        W z (∏ i, (x i : ℕ)) a *
          sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [pivot_retained_pairwise_iff P hP x (L a) (U z)]
      simp only [hx, false_and, ite_false]
    rw [hz, mul_zero]

end Ostmann

end OAI

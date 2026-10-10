import OAI.NumberTheory.Ostmann.Construction.ConstituentScheduledNext
import OAI.NumberTheory.Ostmann.Construction.ConstituentGuardedCopiedAmplitude
import OAI.NumberTheory.Ostmann.Construction.CopiedAmplitudeFubini

namespace OAI

/-! # The guarded next expectation is the actual arithmetic off-diagonal -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def copiedConstituentHistory {D : Type*} {n : ℕ}
    (hist : D → FrequencyTree ℤ n) (V : ℕ) :
    (transferFrequencyRange V) × (D × D) → FrequencyTree ℤ (n + 1) :=
  fun a => (a.1.val, hist a.2.1, hist a.2.2)

theorem constituentPrimeGuardedAmplitude_next {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ u, ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1)) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf (copiedConstituentHistory hist V) center =
      ∑ u, ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        scheduledNextAmplitude ρ χ initialCompleteGraph pivot (initialRegularUnary χ κ)
          n (fun a => hist a.2) (fun a h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
          (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u) T V := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  rw [constituentPrimeGuardedAmplitude_copied]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [constituentScheduledNextAmplitude_eq role size χ κ pivot n p hp P hP Q
    childBound pivotBound ranges leaf hist u center K V T hTpos hTbound
    (hTfull u) (hcut u) hscale hlarge (hgap u) (hrange u)]
  let w (l : CopyScheduleH ρ n → P) : ℂ :=
    ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ)
  let F (s : ℤ) (l : CopyScheduleH ρ n → P) (d : D)
      (r : CopyScheduleH ρ n → P) (d' : D) : ℂ :=
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (copiedConstituentAtomValues role size n P u l r) (s, hist d, hist d') *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ)) then
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center else 0)
  simp only [Complex.ofReal_mul, mul_assoc]
  change (∑ l, w l * ∑ r, w r *
    ∑ a : (transferFrequencyRange V) × (D × D), F a.1.val l a.2.1 r a.2.2) =
    ∑ s ∈ transferFrequencyRange V, ∑ l, ∑ d, ∑ r, ∑ d', w l * (w r * F s l d r d')
  have hs (l r : CopyScheduleH ρ n → P) :=
    copiedFrequency_sum (transferFrequencyRange V) (fun s d d' => F s l d r d')
  simp_rw [hs]
  exact copied_prior_sum_reorder (transferFrequencyRange V) w F

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.ConstituentReconstructedProduct
import OAI.NumberTheory.Ostmann.Construction.ScheduledCopiedSamplePhase
import OAI.NumberTheory.Ostmann.Construction.ScheduledCopiedAmplitude

namespace OAI

/-! # The complete reconstructed sum with actual original-prior coefficients -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentScheduledNextAmplitude_eq {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1)) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    scheduledNextAmplitude ρ χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (fun a => hist a.2) (fun a h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
      (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u) T V =
    ∑ s ∈ transferFrequencyRange V, ∑ l, ∑ d, ∑ r, ∑ d',
      (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, hist d, hist d') *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ)) then
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center else 0) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold scheduledNextAmplitude
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d' _
  have hc := constituentTransferWeight_reconstructed_product role size n p hp P hP Q
    childBound pivotBound ranges leaf u l r s (hist d) (hist d') K V T hTpos hTbound
    (hTfull l d) (fun M hM => hcut M hM (l, d)) (fun M hM => hcut M hM (r, d'))
    hscale hlarge (fun M hM => hgap M hM (l, d) (r, d'))
    (fun M hM => hrange M hM (l, d) (r, d'))
  have hphase := scheduledSamplePhase_copied ρ χ κ pivot n (s, hist d, hist d') P hP u l r center
  calc
    _ = (if validTransferredPivot T
          (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
           frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s then
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u
            (reconstructedPivot (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
              frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s) (l, d) *
          conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u
            (reconstructedPivot (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
              frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s) (r, d')) else 0) *
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center := by
      split_ifs
      · rw [hphase]
      · simp only [zero_mul]
    _ = _ := by
      have hwl (M) : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M (l, d) =
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, hist d) := rfl
      have hwr (M) : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M (r, d') =
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, hist d') := rfl
      simp_rw [hwl, hwr]
      rw [hc]
      split_ifs <;> ring

end Ostmann

end OAI

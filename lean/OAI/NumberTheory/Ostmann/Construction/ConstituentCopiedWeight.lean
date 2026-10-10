import OAI.NumberTheory.Ostmann.Construction.ConstituentTransferWeight
import OAI.NumberTheory.Ostmann.Construction.FullCopiedWeight

namespace OAI

/-! # The exact product of the two arithmetic branch coefficients -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def copiedConstituentAtomValues {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    CopyScheduleAtoms role (n + 1) → ℕ :=
  scheduledCopiedAssignment role n
    (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
    (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
    (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))

/-- The two old coefficients multiply to the next full coefficient with
exactly two original H priors; no outside prior is squared here. -/
theorem constituentTransferWeight_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M)
    (hroot : fullAtomRootGuard role ranges n (copiedConstituentAtomValues role size n P u l r) M s)
    (hL : Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)))
    (hR : Pairwise (fun i j =>
      (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) j))) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, t, t') := by
  unfold constituentTransferWeight
  simp only [hL, hR, ite_true]
  unfold constituentCurrentWeight
  change _ = _ * fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
    (scheduledCopiedAssignment role n
      (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
      (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
      (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))) (s, t, t')
  unfold copiedConstituentAtomValues at hroot
  rw [fullAtomTransferWeight_copied role childBound pivotBound ranges leaf n _ _ _ s t t' M hP,
    ite_eq_left hroot]
  simp only [id_eq, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end Ostmann

end OAI

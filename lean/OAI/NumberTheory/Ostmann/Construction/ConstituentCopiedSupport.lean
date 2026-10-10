import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedWeight
import OAI.NumberTheory.Ostmann.Construction.ConstituentAtomSupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledCopiedSupport
import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedAmplitude

namespace OAI

/-! # The actual arithmetic coefficients supply the next full root guard -/

namespace Ostmann

open scoped BigOperators Classical

theorem copiedConstituentAtomValues_left {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ =
      ∏ h, (l h : ℕ) := by
  unfold copiedConstituentAtomValues
  rw [scheduleAtomLeft_copied, constituentH_product role size n (fun h => (l h : ℕ))]

theorem copiedConstituentAtomValues_right {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ =
      ∏ h, (r h : ℕ) := by
  unfold copiedConstituentAtomValues
  rw [scheduleAtomRight_copied, constituentH_product role size n (fun h => (r h : ℕ))]

/-- No new support assumption is imposed on the next coefficient. Its
coprimality tests follow from nonzero old coefficients and the signed equation;
only the explicit numerical and interval cutoffs are needed. -/
theorem constituentTransferWeight_copied_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M K V : ℕ)
    (hl : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0)
    (hr : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0)
    (hs : s ≠ 0) (hMpos : 0 < M) (hMbound : M ≤ pivotBound n)
    (hrel : frequencyRoot n t * (∏ h, (r h : ℕ)) -
      frequencyRoot n t' * (∏ h, (l h : ℕ)) = s * M)
    (ht : (frequencyRoot n t).natAbs ≤ childBound n)
    (ht' : (frequencyRoot n t').natAbs ≤ childBound n)
    (hlK : (∏ h, (l h : ℕ)) ≤ K) (hrK : (∏ h, (r h : ℕ)) ≤ K)
    (hscale : 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : 2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M ∧
    fullAtomRootGuard role ranges n (copiedConstituentAtomValues role size n P u l r) M s ∧
    Pairwise (fun i j =>
      ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  obtain ⟨hL, hML, _⟩ := constituentTransferWeight_support role size n p hp P Q
    childBound pivotBound ranges leaf id u M (l, t) hl
  obtain ⟨hR, hMR, hMw⟩ := constituentTransferWeight_support role size n p hp P Q
    childBound pivotBound ranges leaf id u M (r, t') hr
  obtain ⟨_, hpair, hM, hfreq⟩ := scheduledCopiedAssignment_support ρ n
    (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
    M (childBound n) K V (frequencyRoot n t) (frequencyRoot n t') s hMpos hs hrel
    ht ht' hlK hrK hscale hL hR hML hMR
    (fun h => hlarge _ (l h).property) (fun h => hlarge _ (r h).property)
    (fun y => hlarge _ (u y).property)
  have hRU : (∏ h, (r h : ℕ)).Coprime s.natAbs := by
    apply Nat.coprime_fintype_prod_left_iff.mpr
    intro h
    simpa only [scheduledCopiedAssignment_right] using
      hfreq (scheduledOutputVertex ρ n (.inl (false, h)))
  have hleft := copiedConstituentAtomValues_left role size n P u l r
  have hright := copiedConstituentAtomValues_right role size n P u l r
  have hnode : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M := by
    refine ⟨hs, ?_, ?_, hMpos, hMbound, ht, ht', ?_, hMw⟩
    · change IsCoprime s (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ)
      rw [hright]
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change Nat.gcd s.natAbs (∏ h, (r h : ℕ)) = 1
      exact hRU.symm
    · change frequencyRoot n t * (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
        frequencyRoot n t' * (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M
      rwa [hleft, hright]
    · change 2 * pivotBound n * childBound n < scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      rwa [hright]
  have hwords := constituent_copied_assignment role size n
    (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ))
  have hguard := constituent_fullAtomRootGuard role size ranges n
    (scheduledCopiedAssignment ρ n (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ)))
    M s hpair hM hfreq (by rw [hwords]; exact hrange)
  have hmap := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
  refine ⟨hnode, ?_, ?_⟩
  · rwa [hwords] at hguard
  · change Pairwise (fun i j =>
      ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) i).Coprime
        ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) j))
    rw [hmap]
    exact hpair

end Ostmann

end OAI

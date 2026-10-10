import OAI.NumberTheory.Ostmann.Construction.TransferPhaseSupport
import OAI.NumberTheory.Ostmann.Construction.CopiedPriorFubini

namespace OAI

/-! # Prime support of the actual copied assignment -/

namespace Ostmann

open scoped BigOperators Classical

/-- The retained tuple has separate H and Y support and coprime total products. -/
theorem retainedPairwise_parts {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ)
    (h : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j))) :
    Pairwise (fun i j => (L i).Coprime (L j)) ∧
      Pairwise (fun i j => (U i).Coprime (U j)) ∧
      (∏ i, L i).Coprime (∏ j, U j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact h (show Sum.inl i ≠ Sum.inl j from fun he => hij (Sum.inl.inj he))
  · intro i j hij
    exact h (show Sum.inr i ≠ Sum.inr j from fun he => hij (Sum.inr.inj he))
  · apply Nat.coprime_fintype_prod_left_iff.mpr
    intro i
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro j
    exact h (show Sum.inl i ≠ Sum.inr j from by intro he; cases he)

/-- Restricting a pairwise copied assignment to either retained branch
recovers its full H/Y coprimality, including cross terms. -/
theorem scheduledCopiedAssignment_pairwise_branch {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ)
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    (h : Pairwise (fun i j =>
      (scheduledCopiedAssignment role n U L R i).Coprime
        (scheduledCopiedAssignment role n U L R j))) (b : Bool) :
    Pairwise (fun i j =>
      (Sum.elim (if b then L else R) U i).Coprime (Sum.elim (if b then L else R) U j)) := by
  let f : CopyScheduleH role n ⊕ CopyScheduleY role n → _ :=
    fun i => scheduledOutputVertex role n (match i with
      | .inl a => .inl (b, a)
      | .inr y => .inr y)
  have hf : Function.Injective f := by
    intro i j hij
    have he := congrArg (copyScheduleSurvivorEquiv role n) hij
    dsimp only [f, scheduledOutputVertex] at he
    simp only [Equiv.apply_symm_apply] at he
    cases i with
    | inl a =>
      cases j with
      | inl a' => exact congrArg Sum.inl (congrArg Prod.snd (Sum.inl.inj he))
      | inr y => cases he
    | inr y =>
      cases j with
      | inl a => cases he
      | inr y' => exact congrArg Sum.inr (Sum.inr.inj he)
  have he (i) : scheduledCopiedAssignment role n U L R (f i) =
      Sum.elim (if b then L else R) U i := by
    cases i with
    | inl a => cases b <;> simp only [f, Bool.false_eq_true, ite_false, ite_true,
        scheduledCopiedAssignment_left, scheduledCopiedAssignment_right, Sum.elim_inl]
    | inr y => exact scheduledCopiedAssignment_outside role n U L R y
  intro i j hij
  rw [← he i, ← he j]
  exact h (hf.ne hij)

/-- Signed reconstruction, the original branch support and the prime cutoff
supply every prime-level test on the next copied assignment. -/
theorem scheduledCopiedAssignment_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (M B K V : ℕ) (v w s : ℤ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hR : Pairwise (fun i j => (Sum.elim R U i).Coprime (Sum.elim R U j)))
    (hML : M.Coprime ((∏ h, L h) * ∏ y, U y))
    (hMR : M.Coprime ((∏ h, R h) * ∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y) :
    let q := scheduledCopiedAssignment role n U L R
    s.natAbs ≤ V ∧ Pairwise (fun i j => (q i).Coprime (q j)) ∧
      (∀ i, M.Coprime (q i)) ∧ (∀ i, (q i).Coprime s.natAbs) := by
  obtain ⟨hLL, hUU, hLU⟩ := retainedPairwise_parts L U hL
  obtain ⟨hRR, _, hRU⟩ := retainedPairwise_parts R U hR
  obtain ⟨hsV, hpair, hM, hunit⟩ := transfer_copied_support_of_ranges L R U M B K V v w s
    hMpos hs hrel hv hw hLbound hRbound hscale hLL hRR hUU hLU hRU
    (Nat.coprime_mul_iff_right.mp hML).1 (Nat.coprime_mul_iff_right.mp hMR).1
    (Nat.coprime_mul_iff_right.mp hML).2 hlargeL hlargeR hlargeU
  have he (i) : scheduledCopiedAssignment role n U L R i =
      transferredLabels L R U (copyScheduleSurvivorEquiv role n i) := by
    unfold scheduledCopiedAssignment
    generalize copyScheduleSurvivorEquiv role n i = j
    rcases j with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  refine ⟨hsV, ?_, ?_, ?_⟩
  · intro i j hij
    simp only [he]
    exact hpair ((copyScheduleSurvivorEquiv role n).injective.ne hij)
  · intro i
    rw [he]
    exact hM _
  · intro i
    rw [he]
    have hc := (ZMod.coe_int_isUnit_iff_isCoprime s _).mp (hunit (copyScheduleSurvivorEquiv role n i))
    have hg := Int.isCoprime_iff_gcd_eq_one.mp hc
    change Nat.gcd (transferredLabels L R U (copyScheduleSurvivorEquiv role n i)) s.natAbs = 1 at hg
    exact hg

end Ostmann

end OAI

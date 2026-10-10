import OAI.NumberTheory.Ostmann.Construction.ScheduleAtomSystem
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSupport

namespace OAI

/-! # A reconstructed pivot inherits coprimality with both H copies -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_pivot_coprime_all {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (x : CopyScheduleAtoms role (n + 1) → ℕ)
    (P : ℕ) (s v w : ℤ)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j)))
    (hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime v.natAbs)
    (hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime w.natAbs)
    (hrel : v * (∏ i : CopyScheduleH role n, (x ⟨.inl (false, i.val), i.property⟩ : ℤ)) -
      w * (∏ i : CopyScheduleH role n, (x ⟨.inl (true, i.val), i.property⟩ : ℤ)) = s * P)
    (hY : ∀ i : CopyScheduleY role n, P.Coprime (x ⟨.inr i.val, i.property⟩)) :
    ∀ i, P.Coprime (x i) := by
  let L := ∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩
  let R := ∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩
  have hLR : L.Coprime R := Nat.coprime_fintype_prod_left_iff.mpr (fun i =>
    Nat.coprime_fintype_prod_right_iff.mpr (fun j => hpair (by
      intro h
      have he := congrArg Subtype.val h
      cases congrArg Prod.fst (Sum.inl.inj he))))
  have hv : IsCoprime v (L : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.gcd v.natAbs L = 1
    exact hleft.symm
  have hw : IsCoprime w (R : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.gcd w.natAbs R = 1
    exact hright.symm
  have hr : v * (R : ℤ) - w * (L : ℤ) = s * 1 * (P : ℤ) := by
    simpa only [L, R, Nat.cast_prod, mul_one] using hrel
  have hcop := (reversal_inherited_coprime v w (L : ℤ) (R : ℤ) s 1 P
    hLR.isCoprime hv hw hr).1
  have hP : P.Coprime (L * R) := Nat.isCoprime_iff_coprime.mp (by
    simpa only [Nat.cast_mul] using hcop)
  have hPL := Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_mul_iff_right.mp hP).1
  have hPR := Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_mul_iff_right.mp hP).2
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl p =>
    rcases p with ⟨b, i⟩
    cases b
    · exact hPR ⟨i, hi⟩
    · exact hPL ⟨i, hi⟩
  | inr i => exact hY ⟨i, hi⟩

end Ostmann

end OAI

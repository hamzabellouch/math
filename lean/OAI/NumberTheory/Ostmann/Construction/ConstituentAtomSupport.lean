import OAI.NumberTheory.Ostmann.Construction.ConstituentWords
import OAI.NumberTheory.Ostmann.Construction.FullAtomTransferWeight

namespace OAI

/-! # The actual constituent support implies the grouped root support -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleConstituentWord_coprime_left {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ) (M : ℕ)
    (hM : ∀ i, M.Coprime (q i)) (v : CopyScheduleAtoms role n) :
    M.Coprime ((scheduleConstituentWord role size n v).map q).prod := by
  rw [scheduleConstituentWord_prod]
  exact Nat.coprime_fintype_prod_right_iff.mpr fun _ => hM _

theorem scheduleConstituentWord_coprime_right {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ) (M : ℕ)
    (hM : ∀ i, (q i).Coprime M) (v : CopyScheduleAtoms role n) :
    ((scheduleConstituentWord role size n v).map q).prod.Coprime M := by
  exact (scheduleConstituentWord_coprime_left role size n q M (fun i => (hM i).symm) v).symm

/-- Every coprimality and frequency-unit component of the next grouped guard
is supplied by the constituent-level arithmetic transfer. -/
theorem constituent_fullAtomRootGuard {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (q : SurvivingConstituent role size (n + 1) → ℕ) (M : ℕ) (s : ℤ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j)))
    (hM : ∀ i, M.Coprime (q i)) (hs : ∀ i, (q i).Coprime s.natAbs)
    (hrange : ∀ r ∈ ranges (n + 1), r.Holds
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map q).prod)) :
    fullAtomRootGuard role ranges n
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map q).prod) M s := by
  exact ⟨scheduleConstituentWord_pairwise role size (n + 1) q hq,
    scheduleConstituentWord_coprime_left role size (n + 1) q M hM,
    scheduleConstituentWord_coprime_right role size (n + 1) q s.natAbs hs, hrange⟩

end Ostmann

end OAI

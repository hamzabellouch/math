import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.Ostmann.Characters.AnchorPairCode

namespace OAI

/-! # The two equally sized final-parity classes of actual copy paths -/

namespace Ostmann

open scoped Classical

theorem copyPathParity_congr_prefix (t u : ℕ → Bool) (n : ℕ)
    (h : ∀ j < n, t j = u j) : copyPathParity t n = copyPathParity u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copyPathParity, h n (Nat.lt_succ_self _), ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem finalCopyParity_snoc {n : ℕ} (t : Fin n → Bool) (b : Bool) :
    finalCopyParity (Fin.snoc t b) = transferCopySign b * finalCopyParity t := by
  have hbefore : copyPathParity (finiteCopyPath (Fin.snoc t b)) n =
      copyPathParity (finiteCopyPath t) n := by
    apply copyPathParity_congr_prefix
    intro j hj
    simp only [finiteCopyPath, hj, Nat.lt_succ_of_lt hj, dite_true]
    exact @Fin.snoc_castSucc n (fun _ => Bool) b t ⟨j, hj⟩
  have hlast : finiteCopyPath (Fin.snoc t b) n = b := by
    simp only [finiteCopyPath, Nat.lt_succ_self, dite_true]
    exact @Fin.snoc_last n (fun _ => Bool) b t
  change transferCopySign (finiteCopyPath (Fin.snoc t b) n) *
      copyPathParity (finiteCopyPath (Fin.snoc t b)) n = _
  rw [hlast, hbefore]
  rfl

abbrev ParityPaths (n : ℕ) (ε : ℤ) := {t : Fin (n + 1) → Bool // finalCopyParity t = ε}

noncomputable def parityPathsEquiv (n : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ParityPaths n ε ≃ (Fin n → Bool) := by
  let f : ParityPaths n ε → (Fin n → Bool) := fun t => Fin.init t.val
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have ha := finalCopyParity_snoc (Fin.init a.val) (a.val (Fin.last n))
    have hb := finalCopyParity_snoc (Fin.init b.val) (b.val (Fin.last n))
    rw [Fin.snoc_init_self, a.property] at ha
    rw [Fin.snoc_init_self, b.property] at hb
    change Fin.init a.val = Fin.init b.val at hab
    have hn : finalCopyParity (Fin.init a.val) ≠ 0 := by
      change copyPathParity (finiteCopyPath (Fin.init a.val)) n ≠ 0
      rcases copyPathParity_sign (finiteCopyPath (Fin.init a.val)) n with h | h <;> omega
    have hl : a.val (Fin.last n) = b.val (Fin.last n) := by
      apply transferCopySign_injective
      apply mul_right_cancel₀ hn
      rw [hab]
      simpa only [hab] using ha.symm.trans hb
    apply Subtype.ext
    calc
      a.val = Fin.snoc (Fin.init a.val) (a.val (Fin.last n)) := (Fin.snoc_init_self _).symm
      _ = Fin.snoc (Fin.init b.val) (b.val (Fin.last n)) := by rw [hab, hl]
      _ = b.val := Fin.snoc_init_self _
  · intro t
    let b : Bool := decide (ε * finalCopyParity t = 1)
    have hp := copyPathParity_sign (finiteCopyPath t) n
    change finalCopyParity t = 1 ∨ finalCopyParity t = -1 at hp
    have he : finalCopyParity (Fin.snoc t b) = ε := by
      rw [finalCopyParity_snoc]
      rcases hε with hε | hε <;> rcases hp with hp | hp <;>
        simp only [b, hε, hp, mul_one, mul_neg_one, neg_neg, decide_true, decide_false,
          show ¬(-1 : ℤ) = 1 by omega, transferCopySign] <;> norm_num
    exact ⟨⟨Fin.snoc t b, he⟩, @Fin.init_snoc n (fun _ => Bool) b t⟩

theorem card_parityPaths (n : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    Fintype.card (ParityPaths n ε) = 2 ^ n := by
  classical
  rw [Fintype.card_congr (parityPathsEquiv n ε hε)]
  simp

noncomputable abbrev FinalParityReassignments (n m : ℕ) :=
  Fin m → (Equiv.Perm (ParityPaths n 1) × Equiv.Perm (ParityPaths n (-1)))

noncomputable instance finalParityReassignmentsFintype (n m : ℕ) :
    Fintype (FinalParityReassignments n m) := by
  classical
  unfold FinalParityReassignments
  exact @Pi.instFintype (Fin m)
    (fun _ => Equiv.Perm (ParityPaths n 1) × Equiv.Perm (ParityPaths n (-1)))
    inferInstance inferInstance (fun _ => inferInstance)

theorem card_finalParityReassignments (n m : ℕ) :
    Fintype.card (FinalParityReassignments n m) = ((Nat.factorial (2 ^ n)) ^ 2) ^ m := by
  classical
  simp only [FinalParityReassignments, Fintype.card_fun, Fintype.card_prod, Fintype.card_perm,
    card_parityPaths n 1 (Or.inl rfl), card_parityPaths n (-1) (Or.inr rfl), Fintype.card_fin]
  rw [pow_two]

end Ostmann

end OAI

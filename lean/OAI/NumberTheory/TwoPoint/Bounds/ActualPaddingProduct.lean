import OAI.NumberTheory.TwoPoint.Bounds.GoodRetainedWordSum
import OAI.NumberTheory.TwoPoint.Walks.WordSegments
import OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords

namespace OAI

/-! Identify recursive padding weights with the literal product at the numerical departures. -/

namespace TwoPointCorrelations

open Finset

theorem paddingWordWeight_eq_prod_sites (Q : Finset ℕ)
    (weight : ℕ → ℤ → ℕ → ℝ) (next : ℕ → ℤ → ℕ → ℤ)
    {m : ℕ} (i : ℕ) (n : ℤ) (q : Fin m → Q) (site : Fin (m + 1) → ℤ)
    (hzero : site 0 = n)
    (hstep : ∀ t : Fin m, site t.succ = next (i + t.val) (site t.castSucc) (q t).val) :
    paddingWordWeight Q weight next i n q =
      ∏ t : Fin m, weight (i + t.val) (site t.castSucc) (q t).val := by
  induction m generalizing i n with
  | zero => simp [paddingWordWeight]
  | succ m ih =>
      rw [paddingWordWeight, Fin.prod_univ_succ]
      have hz : site (Fin.succ 0) = next i n (q 0).val := by
        simpa only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero, hzero] using hstep 0
      have hs : ∀ t : Fin m, (fun u : Fin (m + 1) => site u.succ) t.succ =
          next (i + 1 + t.val) ((fun u : Fin (m + 1) => site u.succ) t.castSucc)
            ((Fin.tail q) t).val := by
        intro t
        simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 t.val,
          Fin.succ_castSucc, Fin.tail] using hstep t.succ
      rw [ih (i + 1) _ (Fin.tail q) (fun u => site u.succ) hz hs]
      simp only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero, hzero]
      congr 1
      apply prod_congr rfl
      intro t _
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 t.val,
        Fin.succ_castSucc, Fin.tail]

lemma wordDisplacement_take_succ (h : ℕ) (word : List SignedStep) (t : ℕ) :
    wordDisplacement h (word.take (t + 1)) =
      wordDisplacement h (word.take t) + wordStepDisplacement h word t := by
  simp only [wordDisplacement_take, sum_range_succ]

theorem paddingWordWeight_eq_departure_product {Q : Finset ℕ} {m : ℕ}
    (h : ℕ) (step : Fin m → SignedStep) (q : Fin m → Q)
    (weight : ℕ → ℤ → ℕ → ℝ) (next : ℕ → ℤ → ℕ → ℤ) (n : ℤ)
    (hnext : ∀ t : Fin m, ∀ z, next t.val z (q t).val = z + (step t).displacement h) :
    paddingWordWeight Q weight next 0 n q =
      ∏ t : Fin m, weight t.val
        (n + wordDisplacement h ((List.ofFn step).take t.val)) (q t).val := by
  let site (t : Fin (m + 1)) := n + wordDisplacement h ((List.ofFn step).take t.val)
  have hz : site 0 = n := by simp [site]
  have hs (t : Fin m) : site t.succ = next (0 + t.val) (site t.castSucc) (q t).val := by
    rw [Nat.zero_add, hnext]
    simp only [site, Fin.val_succ, Fin.val_castSucc, wordDisplacement_take_succ]
    have ht : wordStepDisplacement h (List.ofFn step) t.val = (step t).displacement h := by
      simp only [wordStepDisplacement, List.getElem?_ofFn, t.isLt, dite_true, Fin.eta,
        Option.map_some, Option.getD_some]
    rw [ht, add_assoc]
  simpa only [Nat.zero_add, site, Fin.val_castSucc] using
    paddingWordWeight_eq_prod_sites Q weight next 0 n q site hz hs

theorem retainedColumnPaddingWeight_eq_departure_product {J k : ℕ}
    {P : Fin J → Finset ℕ} (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (h : ℕ) (n : ℤ) (w : ColumnPrimeAssignment J (2 * k) P)
    (forward : Fin (2 * k) → Bool) (q : Fin (2 * k) → Q)
    (hnext : ∀ i : Fin (2 * k), ∀ z, next w i.val z (q i).val =
      z + (SignedStep.mk (forward i) (columnTuple w i) (q i).val).displacement h) :
    retainedColumnPaddingWeight Q u eligible g L K extra next n w q =
      ∏ i : Fin (2 * k), retainedPaddingAtom Q u (eligible w i.val) g L K (extra w i.val)
        (n + wordDisplacement h ((columnTupleWord w forward (fun i => (q i).val)).take i.val))
        (q i).val := by
  exact paddingWordWeight_eq_departure_product h
    (fun i => SignedStep.mk (forward i) (columnTuple w i) (q i).val) q
    (fun i z r => retainedPaddingAtom Q u (eligible w i) g L K (extra w i) z r)
    (next w) n hnext

end TwoPointCorrelations

end OAI

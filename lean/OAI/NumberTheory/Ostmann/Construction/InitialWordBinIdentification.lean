import OAI.NumberTheory.Ostmann.Construction.InitialWordRanges

namespace OAI

/-! # The actual depth-zero atom ranges are exactly the two word-bin events -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialWordBinRanges {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ) :
    List (ScheduleAtomRange role 0) :=
  [initialWordBinRange role true j, initialWordBinRange role false j]

theorem initialWordBinRange_ordered {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (j : ℕ)
    (y : Fin ((k + m) + (k + m)) → ℕ) (b : Bool) :
    (initialWordBinRange role b j).Holds
      (fun a => ∏ i, y (initialWordTupleEquiv k m s cell ⟨a.val, i⟩)) ↔
    ((∏ i : Fin k, (if b then ((wordCopyEquiv ℕ k m).symm y).1.1 i
      else ((wordCopyEquiv ℕ k m).symm y).2.1 i) : ℕ) : ℝ) ∈
      Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  simp only [initialWordBinRange, ScheduleAtomRange.Holds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  cases b with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hp : (∏ i : Fin k, y (initialWordTupleEquiv k m s cell ⟨(false, none), i⟩)) =
          ∏ i, ((wordCopyEquiv ℕ k m).symm y).2.1 i :=
        Finset.prod_congr rfl (fun i _ => (initialWordTuple_negative_word k m s cell y i).symm)
      exact Iff.of_eq (congrArg (fun n : ℕ => (n : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) hp)
  | true =>
      simp only [ite_true]
      have hp : (∏ i : Fin k, y (initialWordTupleEquiv k m s cell ⟨(true, none), i⟩)) =
          ∏ i, ((wordCopyEquiv ℕ k m).symm y).1.1 i :=
        Finset.prod_congr rfl (fun i _ => (initialWordTuple_positive_word k m s cell y i).symm)
      exact Iff.of_eq (congrArg (fun n : ℕ => (n : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) hp)

theorem initialWordBinRanges_ordered {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (j : ℕ)
    (y : Fin ((k + m) + (k + m)) → ℕ) :
    (∀ r ∈ initialWordBinRanges role j,
      r.Holds (fun a => ∏ i, y (initialWordTupleEquiv k m s cell ⟨a.val, i⟩))) ↔
    (((∏ i, ((wordCopyEquiv ℕ k m).symm y).1.1 i : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) ∧
      ((∏ i, ((wordCopyEquiv ℕ k m).symm y).2.1 i : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) := by
  simp only [initialWordBinRanges, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, initialWordBinRange_ordered, ite_true,
    Bool.false_eq_true, ite_false]

theorem initialWordBinRanges_iff_bin {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (τ : ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1)) (y : Fin (((a + 1) + m) + ((a + 1) + m)) → P)
    (hpos : (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ)
    (hneg : (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    (∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun atom => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨atom.val, i⟩) : ℕ))) ↔
    (wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
      wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b) := by
  have hmap := wordCopyEquiv_map (fun p : P => (p : ℕ))
    ((wordCopyEquiv P (a + 1) m).symm y)
  rw [Equiv.apply_symm_apply] at hmap
  have hi := congrArg (wordCopyEquiv ℕ (a + 1) m).symm hmap
  rw [Equiv.symm_apply_apply] at hi
  refine (initialWordBinRanges_ordered role (a + 1) m s cell b.val
    (fun i => (y i : ℕ))).trans ?_
  have hp : (∏ i, ((wordCopyEquiv ℕ (a + 1) m).symm (fun j => (y j : ℕ))).1.1 i) =
      ∏ i, (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℕ) :=
    Finset.prod_congr rfl (fun i _ => (congrFun (congrArg (fun z => z.1.1) hi) i).symm)
  have hn : (∏ i, ((wordCopyEquiv ℕ (a + 1) m).symm (fun j => (y j : ℕ))).2.1 i) =
      ∏ i, (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℕ) :=
    Finset.prod_congr rfl (fun i _ => (congrFun (congrArg (fun z => z.2.1) hi) i).symm)
  rw [hp, hn]
  exact and_congr (wordLogBin_eq_iff_integer_range P hP τ _ b hpos).symm
    (wordLogBin_eq_iff_integer_range P hP τ _ b hneg).symm

end Ostmann

end OAI

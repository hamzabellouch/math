import OAI.NumberTheory.Ostmann.Construction.WordRangePolynomial

namespace OAI

/-! # Inherited frequency-unit tests along the actual word reconstruction -/

namespace Ostmann

open scoped Classical

structure HistoryUnitGuard (σ : Type*) where
  formula : HistoryFormula σ
  modulus : ℕ

noncomputable def HistoryUnitGuard.Holds {σ : Type*} (g : HistoryUnitGuard σ) (a : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.formula.cleared.numerator)
    g.formula.cleared.denominator g.modulus

noncomputable def WordRange.toUnitGuard {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (s : ℤ) : HistoryUnitGuard σ :=
  ⟨(r.toHistory env).formula, s.natAbs⟩

theorem WordRange.toUnitGuard_holds {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (s : ℤ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (r.toUnitGuard env s).Holds a ↔ ((r.word.map x).prod).Coprime s.natAbs := by
  have hval := BranchingWordHistory.wordFormula_value r.word env (fun j => (a j : ℚ))
    (fun i => (x i : ℤ)) (fun i => by simpa only [Int.cast_natCast] using henv i)
  have hprod : (r.word.map (fun i => (x i : ℤ))).prod = ((r.word.map x).prod : ℤ) := by
    induction r.word with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [hprod] at hval
  change smallDivisionTest
    (MvPolynomial.eval₂Hom (RingHom.id ℤ) a (r.toHistory env).formula.cleared.numerator)
    (r.toHistory env).formula.cleared.denominator s.natAbs ↔ _
  dsimp only [WordRange.toHistory]
  rw [HistoryFormula.smallDivisionTest_of_value _ a _ hval s.natAbs]
  simpa only [Int.cast_natCast] using ZMod.isUnit_iff_coprime (r.word.map x).prod s.natAbs

/-- The same word lists that specify ranges also specify product-unit tests.
The interval endpoints are irrelevant for this additional support family. -/
noncomputable def WordRangeDecoration.UnitsAt {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf ranges, .leaf _, x, v => ∀ r ∈ ranges, ((r.word.map x).prod).Coprime v.natAbs
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ q ∈ ranges, ((q.word.map x).prod).Coprime t.1.natAbs) ∧
        L.UnitsAt l (Function.update x d.target P) t.2.1 ∧
        R.UnitsAt r (Function.update x d.target P) t.2.2

noncomputable def WordRangeDecoration.unitGuards {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryUnitGuard σ)
  | 0, .leaf ranges, .leaf _, v, _, env => ranges.map (fun r => r.toUnitGuard env v)
  | n + 1, .node ranges L R, .node d l r, t, ht, env =>
      let next := BranchingWordHistory.updatedFormulas
        (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1) env
      ranges.map (fun q => q.toUnitGuard env t.1) ++
        (L.unitGuards l t.2.1 ht.2.1 next ++ R.unitGuards r t.2.2 ht.2.2 next)

/-- The quotient residues retain every inherited frequency-unit condition,
including at terminal leaves and at previously reconstructed pivots. -/
theorem WordRangeDecoration.unitGuards_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ g ∈ D.unitGuards template t ht env, g.Holds a) ↔ D.UnitsAt template x t := by
  induction template generalizing env x with
  | leaf word =>
    cases D with
    | leaf ranges =>
      simp only [unitGuards, UnitsAt, List.forall_mem_map]
      exact forall₂_congr fun r _ => r.toUnitGuard_holds env t a x henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      simp only [unitGuards, List.forall_mem_append, List.forall_mem_map, UnitsAt, hp.historyPivot_eq]
      apply and_congr (forall₂_congr fun q _ => q.toUnitGuard_holds env t.1 a x henv)
      exact and_congr (ihL L t.2.1 ht.2.1 _ _ hu hvL) (ihR R t.2.2 ht.2.2 _ _ hu hvR)

theorem WordRangeDecoration.unitGuards_length {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.unitGuards template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; simp only [unitGuards, count, List.length_map]
  | node d l r ihL ihR =>
    cases D
    simp only [unitGuards, count, List.length_append, List.length_map, ihL, ihR]
    omega

theorem WordRangeDecoration.unitGuards_formulas {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.unitGuards template t ht env).map HistoryUnitGuard.formula =
      (D.formulas template t ht env).map HistoryRange.formula := by
  induction template generalizing env with
  | leaf word =>
    cases D
    simp only [unitGuards, formulas, List.map_map, Function.comp_def, WordRange.toUnitGuard]
  | node d l r ihL ihR =>
    cases D
    simp only [unitGuards, formulas, List.map_append, ihL, ihR, List.map_map,
      Function.comp_def, WordRange.toUnitGuard]

end Ostmann

end OAI

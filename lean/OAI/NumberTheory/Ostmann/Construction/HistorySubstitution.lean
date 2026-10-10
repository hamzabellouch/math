import OAI.NumberTheory.Ostmann.Construction.HistoryFormula

namespace OAI

/-! # Substitution constructs the actual rational expressions of a reversed history -/

namespace Ostmann.HistoryFormula

variable {σ τ : Type*}

noncomputable def value (F : HistoryFormula σ) (x : σ → ℚ) : ℚ := F.cleared.eval x

def bind (f : σ → HistoryFormula τ) : HistoryFormula σ → HistoryFormula τ
  | .prime i => f i
  | .external z => .external z
  | .product l r => .product (l.bind f) (r.bind f)
  | .solve l r v w s hs => .solve (l.bind f) (r.bind f) v w s hs

@[simp] theorem value_prime (i : σ) (x : σ → ℚ) : (prime i).value x = x i :=
  ClearedHistoryValue.eval_variable i x

@[simp] theorem value_external (z : ℤ) (x : σ → ℚ) : (external z).value x = z :=
  ClearedHistoryValue.eval_constant z x

@[simp] theorem value_product (l r : HistoryFormula σ) (x : σ → ℚ) :
    (product l r).value x = l.value x * r.value x := by
  simp only [value, cleared, ClearedHistoryValue.eval_prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, ite_true]

@[simp] theorem value_solve (l r : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0) (x : σ → ℚ) :
    (solve l r v w s hs).value x = (v * r.value x - w * l.value x) / s :=
  ClearedHistoryValue.eval_pivot l.cleared r.cleared v w s hs x

theorem value_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (x : τ → ℚ) :
    (F.bind f).value x = F.value (fun i => (f i).value x) := by
  induction F with
  | prime i => simp only [bind, value_prime]
  | external z => simp only [bind, value_external]
  | product l r hl hr => simp only [bind, value_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, value_solve, hl, hr]

/-- A fixed number of substitutions multiplies the expression-size bound;
for fixed transfer depth this remains a polynomial in the word length. -/
theorem cost_bind_le (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (C : ℕ) (hC : 1 ≤ C) (hf : ∀ i, (f i).cost ≤ C) :
    (F.bind f).cost ≤ C * F.cost := by
  induction F with
  | prime i => simpa only [bind, cost, Nat.mul_one] using hf i
  | external z => simpa only [bind, cost, Nat.mul_one] using hC
  | product l r hl hr =>
    simpa only [bind, cost, Nat.mul_add] using Nat.add_le_add hl hr
  | solve l r v w s hs hl hr =>
    simp only [bind, cost, Nat.mul_add]
    have hc2 : 2 ≤ C * 2 := by omega
    omega

theorem inputsBounded_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (R : ℝ)
    (hF : F.InputsBounded R) (hf : ∀ i, (f i).InputsBounded R) :
    (F.bind f).InputsBounded R := by
  induction F with
  | prime i => exact hf i
  | external z => exact hF
  | product l r hl hr => exact ⟨hl hF.1, hr hF.2⟩
  | solve l r v w s hs hl hr => exact ⟨hl hF.1, hr hF.2.1, hF.2.2⟩

noncomputable def listProduct : List (HistoryFormula σ) → HistoryFormula σ
  | [] => .external 1
  | f :: fs => .product f (listProduct fs)

theorem value_listProduct (fs : List (HistoryFormula σ)) (x : σ → ℚ) :
    (listProduct fs).value x = (fs.map (fun F => F.value x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, value_product, List.map_cons, List.prod_cons, ih]

theorem cost_listProduct (fs : List (HistoryFormula σ)) :
    (listProduct fs).cost = (fs.map cost).sum + 1 := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [listProduct, cost, List.map_cons, List.sum_cons, ih]; omega

noncomputable def replace [DecidableEq σ] (F : HistoryFormula σ) (i : σ)
    (replacement : HistoryFormula σ) : HistoryFormula σ :=
  F.bind (fun j => if j = i then replacement else .prime j)

theorem value_replace [DecidableEq σ] (F : HistoryFormula σ) (i : σ)
    (replacement : HistoryFormula σ) (x : σ → ℚ) :
    (F.replace i replacement).value x = F.value (Function.update x i (replacement.value x)) := by
  rw [replace, value_bind]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp only [hj, ite_false, value_prime, Function.update_of_ne hj]

end Ostmann.HistoryFormula

end OAI

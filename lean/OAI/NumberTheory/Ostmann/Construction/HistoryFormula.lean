import OAI.NumberTheory.Ostmann.Arithmetic.ClearedHistoryBounds

namespace OAI

/-! # The actual product-and-pivot formulas of a fixed arithmetic history -/

namespace Ostmann

inductive HistoryFormula (σ : Type*) where
  | prime (i : σ)
  | external (z : ℤ)
  | product (left right : HistoryFormula σ)
  | solve (left right : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0)

namespace HistoryFormula

variable {σ : Type*}

noncomputable def cleared : HistoryFormula σ → ClearedHistoryValue σ
  | .prime i => .ofVariable i
  | .external z => .constant z
  | .product f g => .prod Finset.univ (fun b : Bool => if b then f.cleared else g.cleared)
  | .solve f g v w s hs => .pivot f.cleared g.cleared v w s hs

def cost : HistoryFormula σ → ℕ
  | .prime _ => 1
  | .external _ => 1
  | .product f g => f.cost + g.cost
  | .solve f g _ _ _ _ => f.cost + g.cost + 2

def frequencies : HistoryFormula σ → List ℤ
  | .prime _ => []
  | .external _ => []
  | .product f g => f.frequencies ++ g.frequencies
  | .solve f g _ _ s _ => s :: (f.frequencies ++ g.frequencies)

def InputsBounded (R : ℝ) : HistoryFormula σ → Prop
  | .prime _ => True
  | .external z => |(z : ℝ)| ≤ R
  | .product f g => f.InputsBounded R ∧ g.InputsBounded R
  | .solve f g v w s _ => f.InputsBounded R ∧ g.InputsBounded R ∧
      |(v : ℝ)| ≤ R ∧ |(w : ℝ)| ≤ R ∧ |(s : ℝ)| ≤ R

theorem degree_le_cost (F : HistoryFormula σ) : F.cleared.numerator.totalDegree ≤ F.cost := by
  induction F with
  | prime i => simp [cleared, cost, ClearedHistoryValue.ofVariable]
  | external z =>
    simp only [cleared, cost, ClearedHistoryValue.constant, MvPolynomial.totalDegree_C]
    omega
  | product f g ihf ihg =>
    apply (ClearedHistoryValue.degree_prod _ _).trans
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, cost] using
      Nat.add_le_add ihf ihg
  | solve f g v w s hs ihf ihg =>
    apply (ClearedHistoryValue.degree_pivot f.cleared g.cleared v w s hs).trans
    exact max_le (by dsimp only [cost]; omega) (by dsimp only [cost]; omega)

theorem denominator_eq_frequency_product (F : HistoryFormula σ) :
    F.cleared.denominator = F.frequencies.prod := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product f g ihf ihg =>
    simp only [cleared, ClearedHistoryValue.prod, Fintype.prod_bool, Bool.false_eq_true,
      ite_false, ite_true, ihf, ihg, frequencies, List.prod_append]
  | solve f g v w s hs ihf ihg =>
    simp only [cleared, ClearedHistoryValue.pivot, ihf, ihg, frequencies, List.prod_cons,
      List.prod_append]
    ring

theorem frequency_count_le_cost (F : HistoryFormula σ) : F.frequencies.length ≤ F.cost := by
  induction F with
  | prime i => simp [frequencies, cost]
  | external z => simp [frequencies, cost]
  | product f g ihf ihg => simp only [frequencies, cost, List.length_append]; omega
  | solve f g v w s hs ihf ihg =>
    simp only [frequencies, cost, List.length_cons, List.length_append]
    omega

/-- The same bound applies after any subset of independent variables is set
to zero; its proof uses only their absolute upper bounds. -/
theorem bounded (F : HistoryFormula σ) (x : σ → ℝ) (R : ℝ) (hR : 3 ≤ R)
    (hx : ∀ i, |x i| ≤ R) (hF : F.InputsBounded R) :
    F.cleared.Bounded x (R ^ F.cost) := by
  have hR0 : 0 ≤ R := by linarith
  induction F with
  | prime i =>
    simpa only [cleared, cost, pow_one] using
      ClearedHistoryValue.bounded_variable i x R (by linarith) (hx i)
  | external z =>
    simpa only [cleared, cost, pow_one] using
      ClearedHistoryValue.bounded_constant z x R (by linarith) hF
  | product f g ihf ihg =>
    have hf := ihf hF.1
    have hg := ihg hF.2
    have hh := ClearedHistoryValue.bounded_prod Finset.univ
      (fun b : Bool => if b then f.cleared else g.cleared) x
      (fun b : Bool => if b then R ^ f.cost else R ^ g.cost)
      (fun b _ => by cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> assumption)
    simpa only [cleared, cost, Fintype.prod_bool, Bool.false_eq_true, ite_false, ite_true,
      ← pow_add, Nat.add_comm] using hh
  | solve f g v w s hs ihf ihg =>
    have hh := ClearedHistoryValue.bounded_pivot f.cleared g.cleared v w s hs x
      (R ^ f.cost) (R ^ g.cost) (ihf hF.1) (ihg hF.2.1)
    have hc : |(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)| ≤ R ^ 2 := by
      obtain ⟨_, _, hv, hw, hs⟩ := hF
      nlinarith
    have hb : (|(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)|) * R ^ f.cost * R ^ g.cost ≤
        R ^ (f.cost + g.cost + 2) := by
      calc
        _ ≤ R ^ 2 * R ^ f.cost * R ^ g.cost := by gcongr
        _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
    exact ⟨hh.1.trans hb, hh.2.trans hb⟩

theorem zero_variable_bound (F : HistoryFormula σ) (i : σ) (x : σ → ℤ)
    (R : ℝ) (hR : 3 ≤ R) (hx : ∀ j, |(x j : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    |((MvPolynomial.eval₂Hom (RingHom.id ℤ) x
      (zeroHistoryVariable i F.cleared.numerator) : ℤ) : ℝ)| ≤ R ^ F.cost := by
  classical
  apply ClearedHistoryValue.zero_variable_value_bound F.cleared i x
  apply F.bounded _ R hR _ hF
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self, Int.cast_zero, abs_zero] using (show 0 ≤ R by linarith)
  · simpa only [Function.update_of_ne hj] using hx j

end HistoryFormula

theorem integer_list_product_dvd_power (l : List ℤ) (M : ℤ) (h : ∀ d ∈ l, d ∣ M) :
    l.prod ∣ M ^ l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd := h d (by simp)
    have hl := ih (fun e he => h e (by simp [he]))
    simpa only [List.prod_cons, List.length_cons, pow_succ, mul_comm] using mul_dvd_mul hd hl

theorem HistoryFormula.denominator_test_period {σ : Type*} (F : HistoryFormula σ)
    (M s : ℤ) (h : ∀ d ∈ F.frequencies, d ∣ M) (hs : s ∣ M) :
    F.cleared.denominator * s ∣ M ^ (F.frequencies.length + 1) := by
  rw [F.denominator_eq_frequency_product, pow_succ]
  exact mul_dvd_mul (integer_list_product_dvd_power _ M h) hs

end Ostmann

end OAI

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Constructive interpolation on finite horizontal rows
-/

section

noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01.RowLagrange
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

/-- Degree bound for a finite product of ordinary linear factors. -/
theorem product_natDegree_le {ι : Type*} (s : Finset ι) (K : ι → F) :
    (∏ i ∈ s, (X - C (K i))).natDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_X_sub_C, Nat.add_comm] using Nat.add_le_add_right ih 1)

def basis (s : Finset F) (x : F) : F[X] :=
  C ((∏ y ∈ s.erase x, (x-y))⁻¹) * ∏ y ∈ s.erase x, (X - C y)

theorem basis_eval_self (s : Finset F) (x : F) : (basis s x).eval x = 1 := by
  classical
  have h : ∏ y ∈ s.erase x, (x-y) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (Finset.mem_erase.mp hy).1.symm
  simp only [basis, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact inv_mul_cancel₀ h

theorem basis_eval_other (s : Finset F) {x y : F} (hxy : x ≠ y) (hy : y ∈ s) :
    (basis s x).eval y = 0 := by
  classical
  simp only [basis, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have h : ∏ z ∈ s.erase x, (y-z) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩) (sub_self _)
  rw [h, mul_zero]

theorem basis_natDegree_le (s : Finset F) (x : F) :
    (basis s x).natDegree ≤ (s.erase x).card :=
  (Polynomial.natDegree_C_mul_le _ _).trans (product_natDegree_le _ id)

def interpolate (s : Finset F) (v : F → F) : F[X] :=
  ∑ x ∈ s, C (v x) * basis s x

theorem interpolate_eval (s : Finset F) (v : F → F) {x : F} (hx : x ∈ s) :
    (interpolate s v).eval x = v x := by
  classical
  simp only [interpolate, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_eq_single x]
  · rw [basis_eval_self, mul_one]
  · intro y hy hyx
    rw [basis_eval_other s hyx hx, mul_zero]
  · intro h
    exact False.elim (h hx)

theorem interpolate_degree_lt (s : Finset F) (v : F → F) :
    (interpolate s v).degree < s.card := by
  classical
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  rw [Nat.cast_withBot]
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe s.card)).2
  intro x hx
  have hdeg : (C (v x) * basis s x).natDegree ≤ s.card - 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by
      simpa [Finset.card_erase_of_mem hx] using basis_natDegree_le s x)
  apply lt_of_le_of_lt (Polynomial.degree_le_natDegree)
  exact WithBot.coe_lt_coe.mpr
    (lt_of_le_of_lt hdeg (Nat.sub_lt (Finset.card_pos.mpr ⟨x,hx⟩) (by decide : 0<1)))

end Nagata.W01.RowLagrange

end
end

section

noncomputable section
open scoped BigOperators
open Polynomial

namespace Nagata.W01

abbrev Plane := ℂ × ℂ

def monomial (b l : ℕ) : Plane → ℂ := fun z => z.1 ^ b * z.2 ^ l

def monomialSpace (q m : ℕ) : Submodule ℂ (Plane → ℂ) :=
  Submodule.span ℂ {f | ∃ b < m, ∃ l < q * (m - b), f = monomial b l}

theorem monomial_mem {q m b l : ℕ} (hb : b < m) (hl : l < q * (m-b)) :
    monomial b l ∈ monomialSpace q m :=
  Submodule.subset_span ⟨b, hb, l, hl, rfl⟩

/-- A product of two univariate polynomials has the advertised monomial support. -/
theorem separable_mem {q m : ℕ} (p Q : ℂ[X])
    (h : ∀ b ∈ p.support, ∀ l ∈ Q.support, b < m ∧ l < q * (m-b)) :
    (fun z : Plane => p.eval z.1 * Q.eval z.2) ∈ monomialSpace q m := by
  have heq : (fun z : Plane => p.eval z.1 * Q.eval z.2) =
      ∑ b ∈ p.support, ∑ l ∈ Q.support,
        (p.coeff b * Q.coeff l) • monomial b l := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, monomial,
      Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [heq]
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.sum_mem
  intro l hl
  exact Submodule.smul_mem _ _ (monomial_mem (h b hb l hl).1 (h b hb l hl).2)

def rowPrefix (K : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range n, (X - C (K i))

theorem rowPrefix_eval (K : ℕ → ℂ) (n : ℕ) (y : ℂ) :
    (rowPrefix K n).eval y = ∏ i ∈ Finset.range n, (y - K i) := by
  simp [rowPrefix, Polynomial.eval_prod]

theorem rowPrefix_eval_earlier (K : ℕ → ℂ) {i n : ℕ} (hi : i < n) :
    (rowPrefix K n).eval (K i) = 0 := by
  rw [rowPrefix_eval]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)

theorem rowPrefix_eval_ne_zero (K : ℕ → ℂ) (n : ℕ)
    (hK : ∀ i < n, K n ≠ K i) : (rowPrefix K n).eval (K n) ≠ 0 := by
  rw [rowPrefix_eval]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hK i (Finset.mem_range.mp hi))

theorem rowPrefix_natDegree_le (K : ℕ → ℂ) (n : ℕ) :
    (rowPrefix K n).natDegree ≤ n := by
  simpa [rowPrefix] using RowLagrange.product_natDegree_le (Finset.range n) K

/-- Ordinary interpolation, with the degree bound retained even for an empty row. -/
theorem exists_row_polynomial (xs : Finset ℂ) (v : ℂ → ℂ) :
    ∃ p : ℂ[X], p.degree < xs.card ∧ ∀ x ∈ xs, p.eval x = v x := by
  exact ⟨RowLagrange.interpolate xs v, RowLagrange.interpolate_degree_lt xs v,
    fun x hx => RowLagrange.interpolate_eval xs v hx⟩

/-- Each row correction belongs to the exact staircase of allowed monomials. -/
theorem correction_mem {q m n : ℕ} (K : ℕ → ℂ) (xs : Finset ℂ) (p : ℂ[X])
    (hp : p.degree < xs.card) (hcard : xs.card ≤ m)
    (horder : n + 1 ≤ q * (m - xs.card + 1)) :
    (fun z : Plane => p.eval z.1 * (rowPrefix K n).eval z.2) ∈ monomialSpace q m := by
  apply separable_mem
  intro b hb l hl
  have hbcard : b < xs.card := by
    exact WithBot.coe_lt_coe.mp
      (lt_of_le_of_lt (Polynomial.le_degree_of_mem_supp b hb) hp)
  have hlbound : l ≤ n :=
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hl)).trans
      (rowPrefix_natDegree_le K n)
  have hsub : m - xs.card + 1 ≤ m - b := by omega
  constructor
  · omega
  · exact lt_of_lt_of_le (by omega : l < q * (m - xs.card + 1))
      (Nat.mul_le_mul_left q hsub)

/-- Constructive interpolation on finitely many ordered rows.
The explicit ordered-row bound is derived from the manuscript row counts separately. -/
theorem interpolate_ordered_rows (q m s : ℕ) (K : ℕ → ℂ) (xs : ℕ → Finset ℂ)
    (hK : ∀ i < s, ∀ j < s, K i = K j → i = j)
    (hcard : ∀ i < s, (xs i).card ≤ m)
    (horder : ∀ i < s, i + 1 ≤ q * (m - (xs i).card + 1))
    (v : Plane → ℂ) :
    ∃ f ∈ monomialSpace q m, ∀ i < s, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  have step : ∀ n ≤ s, ∃ f ∈ monomialSpace q m,
      ∀ i < n, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      intro i hi
      omega
    | succ n ih =>
      intro hn
      obtain ⟨f, hf, hfv⟩ := ih (by omega)
      have hns : n < s := by omega
      have hQ : (rowPrefix K n).eval (K n) ≠ 0 := by
        apply rowPrefix_eval_ne_zero
        intro i hi heq
        have := hK n hns i (by omega) heq
        omega
      obtain ⟨p, hp, hpv⟩ := exists_row_polynomial (xs n)
        (fun x => (v (x, K n) - f (x, K n)) / (rowPrefix K n).eval (K n))
      let c : Plane → ℂ := fun z => p.eval z.1 * (rowPrefix K n).eval z.2
      refine ⟨f + c, Submodule.add_mem _ hf
        (correction_mem K (xs n) p hp (hcard n hns) (horder n hns)), ?_⟩
      intro i hi x hx
      by_cases hin : i = n
      · subst i
        change f (x, K n) + p.eval x * (rowPrefix K n).eval (K n) = v (x, K n)
        rw [hpv x hx, div_mul_cancel₀ _ hQ]
        ring
      · have hil : i < n := by omega
        change f (x, K i) + p.eval x * (rowPrefix K n).eval (K i) = v (x, K i)
        rw [rowPrefix_eval_earlier K hil, mul_zero, add_zero, hfv i hil x hx]
  exact step s le_rfl

/-- The same construction with rows indexed by `Fin s`. -/
theorem interpolate_fin_rows (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hcard : ∀ i, (xs i).card ≤ m)
    (horder : ∀ i, i.val + 1 ≤ q * (m - (xs i).card + 1))
    (v : Plane → ℂ) :
    ∃ f ∈ monomialSpace q m, ∀ i, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  let K' : ℕ → ℂ := fun i => if h : i < s then K ⟨i, h⟩ else 0
  let xs' : ℕ → Finset ℂ := fun i => if h : i < s then xs ⟨i, h⟩ else ∅
  have hK' : ∀ i < s, ∀ j < s, K' i = K' j → i = j := by
    intro i hi j hj heq
    have h := hK (by simpa [K', hi, hj] using heq)
    exact congrArg Fin.val h
  have hcard' : ∀ i < s, (xs' i).card ≤ m := by
    intro i hi
    simpa [xs', hi] using hcard ⟨i, hi⟩
  have horder' : ∀ i < s, i + 1 ≤ q * (m - (xs' i).card + 1) := by
    intro i hi
    simpa [xs', hi] using horder ⟨i, hi⟩
  obtain ⟨f, hf, hv⟩ := interpolate_ordered_rows q m s K' xs' hK' hcard' horder' v
  refine ⟨f, hf, ?_⟩
  intro i x hx
  have hx' : x ∈ xs' i.val := by simpa [xs', i.isLt] using hx
  simpa [K', i.isLt] using hv i.val i.isLt x hx'

/-- Evaluation in two actual polynomial indeterminates. -/
def planeEval (p : MvPolynomial (Fin 2) ℂ) : Plane → ℂ :=
  fun z => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2) p

/-- The corresponding subspace inside the actual bivariate polynomial ring. -/
def polynomialSpace (q m : ℕ) : Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  Submodule.span ℂ {p | ∃ b < m, ∃ l < q * (m - b),
    p = MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l}

/-- Realization preserves the exact span of permitted bivariate monomials. -/
theorem exists_polynomialSpace_of_mem {q m : ℕ} {f : Plane → ℂ}
    (hf : f ∈ monomialSpace q m) :
    ∃ p ∈ polynomialSpace q m, planeEval p = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hf
    refine ⟨MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l,
      Submodule.subset_span ⟨b, hb, l, hl, rfl⟩, ?_⟩
    funext z
    simp [planeEval, monomial]
  | zero =>
    exact ⟨0, Submodule.zero_mem _, by funext z; simp [planeEval]⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨p, hp, rfl⟩ := ihf
    obtain ⟨Q, hQ, rfl⟩ := ihg
    exact ⟨p + Q, Submodule.add_mem _ hp hQ, by funext z; simp [planeEval]⟩
  | smul a f hf ih =>
    obtain ⟨p, hp, rfl⟩ := ih
    exact ⟨a • p, Submodule.smul_mem _ a hp, by funext z; simp [planeEval]⟩

/-- Ordered-row interpolation inside the actual bivariate polynomial ring. -/
theorem interpolate_fin_rows_polynomial (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hcard : ∀ i, (xs i).card ≤ m)
    (horder : ∀ i, i.val + 1 ≤ q * (m - (xs i).card + 1))
    (v : Plane → ℂ) :
    ∃ p ∈ polynomialSpace q m, ∀ i, ∀ x ∈ xs i,
      planeEval p (x, K i) = v (x, K i) := by
  obtain ⟨f, hf, hv⟩ := interpolate_fin_rows q m s K xs hK hcard horder v
  obtain ⟨p, hp, hpf⟩ := exists_polynomialSpace_of_mem hf
  exact ⟨p, hp, by simpa [hpf] using hv⟩

/-- The function-space formulation has actual bivariate polynomial representatives. -/
theorem exists_mvPolynomial_of_mem {q m : ℕ} {f : Plane → ℂ}
    (hf : f ∈ monomialSpace q m) :
    ∃ p : MvPolynomial (Fin 2) ℂ, planeEval p = f := by
  obtain ⟨p, _, hpf⟩ := exists_polynomialSpace_of_mem hf
  exact ⟨p, hpf⟩

end Nagata.W01

end
end

end OAI

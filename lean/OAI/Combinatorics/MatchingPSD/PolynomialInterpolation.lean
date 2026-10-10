import OAI.Combinatorics.MatchingPSD.MatrixAverages

namespace OAI

namespace MatchingInterpolation
open Polynomial
open MatchingSmoothing

abbrev Point := Fin 3 → ℝ
abbrev GridIndex (d : ℕ) := Fin 3 → Fin (d+1)
def coord (i : Fin 3) (x : Point) : ℝ := x i
noncomputable def lagrange (d : ℕ) (k : Fin (d+1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (fun j : Fin (d+1) => (j:ℝ)) k
noncomputable def tensorBasis (d : ℕ) (g : GridIndex d) (x : Point) : ℝ :=
  ∏ a, (lagrange d (g a)).eval (x a)
def gridNode {d : ℕ} (g : GridIndex d) : Point := fun a => (g a:ℝ)

lemma power_interpolation (d k : ℕ) (hk : k ≤ d) (x : ℝ) :
    x^k = ∑ j : Fin (d+1), (j:ℝ)^k * (lagrange d j).eval x := by
  have hinj : Set.InjOn (fun j : Fin (d+1) => (j:ℝ)) (Finset.univ : Finset (Fin (d+1))) := by
    intro i _ j _ h
    apply Fin.ext
    change (i.val:ℝ) = (j.val:ℝ) at h
    exact Nat.cast_inj.mp h
  have hdeg : (Polynomial.X^k : ℝ[X]).degree < (Finset.univ : Finset (Fin (d+1))).card := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hk
  have he := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate hinj hdeg)
  simpa [Lagrange.interpolate_apply, lagrange, Polynomial.eval_finsetSum] using he

lemma list_product_counts (l : List (Fin 3)) (x : Point) :
    (l.map x).prod = ∏ a, x a ^ l.count a := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  have hn : a ∉ l := fun hx => ha (List.mem_toFinset.mpr hx)
  simp [List.count_eq_zero_of_not_mem hn]

lemma monomial_interpolation (d : ℕ) (l : List (Fin 3)) (hl : l.length ≤ d) (x : Point) :
    (l.map x).prod = ∑ g : GridIndex d, tensorBasis d g x * (l.map (gridNode g)).prod := by
  rw [list_product_counts]
  have hp (a : Fin 3) := power_interpolation d (l.count a)
    (List.count_le_length.trans hl) (x a)
  simp_rw [hp]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib, list_product_counts, mul_comm]
  rfl

lemma lowDegree_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (x : Point) : P x = ∑ g : GridIndex d, tensorBasis d g x * P (gridNode g) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have he (v : Point) : (l.map coord).prod v = (l.map v).prod := by
      induction l with
      | nil => rfl
      | cons a l ih => simpa [coord] using congrArg (fun t => v a*t) (ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ l.length) hl))
    simp_rw [he]
    exact monomial_interpolation d l hl x
  | zero => simp
  | add f g _ _ hf hg => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hf, hg]
  | smul c f _ hf =>
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm _ c, Finset.mul_sum, hf]

noncomputable def linePolynomial (d : ℕ) (g : GridIndex d) (v : Point) : ℝ[X] :=
  ∏ a, (lagrange d (g a)).comp (Polynomial.C (v a) * Polynomial.X)

lemma linePolynomial_eval (d : ℕ) (g : GridIndex d) (v : Point) (t : ℝ) :
    (linePolynomial d g v).eval t = tensorBasis d g (fun a => t * v a) := by
  simp only [linePolynomial, tensorBasis, Polynomial.eval_prod, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro a _
  rw [mul_comm]

lemma linePolynomial_zero (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 0 = ∏ a, (lagrange d (g a)).eval 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, linePolynomial_eval]
  simp [tensorBasis]

lemma linePolynomial_one (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 1 =
      ∑ a, v a * ((∏ b ∈ Finset.univ.erase a, (lagrange d (g b)).eval 0) *
        (lagrange d (g a)).derivative.eval 0) := by
  have he (P : ℝ[X]) : P.coeff 1 = P.derivative.eval 0 := by
    simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  rw [he, linePolynomial, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero]
  ring

def origin : Point := ![1,0,0]
def dirA : Point := ![0,2,0]
def dirB : Point := ![0,0,2]
def dirStar : Point := ![2,0,0]
def dirP : Point := ![-1,1,1]
noncomputable def weightPolynomial (d : ℕ) (g : GridIndex d) : ℝ[X] :=
  linePolynomial d g dirA + linePolynomial d g dirB - linePolynomial d g dirStar -
    (2:ℝ) • linePolynomial d g dirP + linePolynomial d g 0

lemma weightPolynomial_zero (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 0 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_zero]
  ring

lemma weightPolynomial_one (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 1 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro a _
  fin_cases a <;> simp [dirA, dirB, dirStar, dirP]

lemma weightPolynomial_bound (d : ℕ) (g : GridIndex d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,
      |(weightPolynomial d g).eval t| ≤ c * t^2 := by
  have hd : (Polynomial.X^2 : ℝ[X]) ∣ weightPolynomial d g := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    interval_cases k
    · exact weightPolynomial_zero d g
    · exact weightPolynomial_one d g
  obtain ⟨P, hP⟩ := hd
  obtain ⟨b, hb⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  refine ⟨max b 0, le_max_right _ _, ?_⟩
  intro t ht
  rw [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, abs_mul,
    abs_of_nonneg (sq_nonneg t), mul_comm]
  have htbound : |P.eval t| ≤ b := by simpa only [Real.norm_eq_abs] using hb t ht
  exact mul_le_mul_of_nonneg_right (htbound.trans (le_max_left b 0)) (sq_nonneg t)

noncomputable def weight (d : ℕ) (L : ℝ) (g : GridIndex d) : ℝ :=
  (weightPolynomial d g).eval L⁻¹

lemma weights_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    ∀ g : GridIndex d, |weight d L g| ≤ c / L^2 := by
  classical
  choose c hc hb using weightPolynomial_bound d
  refine ⟨1 + ∑ g, c g, by have hsum := Finset.sum_nonneg (fun g (_ : g ∈ Finset.univ) => hc g); linarith, ?_⟩
  intro L hL g
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht : L⁻¹ ∈ Set.Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hLp.le,
    (inv_le_one₀ hLp).mpr hL⟩
  calc
    |weight d L g| ≤ c g * (L⁻¹)^2 := hb g L⁻¹ ht
    _ ≤ (1+∑ a, c a) * (L⁻¹)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hc a)
        (Finset.mem_univ g)
      linarith
    _ = (1+∑ a, c a)/L^2 := by simp [div_eq_mul_inv]

lemma lowDegree_affine_pullback (d : ℕ) (P : Point → ℝ)
    (hP : P ∈ lowDegree coord d) (b : Point) (L : ℝ) :
    (fun x : Point => P (fun a => b a + L*x a)) ∈ lowDegree coord d := by
  have hcoord (a : Fin 3) : (fun x : Point => b a + L*x a) ∈ lowDegree coord 1 := by
    have hc := (lowDegree coord 1).smul_mem (b a) (one_mem_lowDegree coord 1)
    have hx := (lowDegree coord 1).smul_mem L (coord_mem_lowDegree coord a)
    convert (lowDegree coord 1).add_mem hc hx using 1
    ext x
    simp [coord]
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    apply lowDegree_mono coord hl
    clear hl
    induction l with
    | nil => exact one_mem_lowDegree coord 0
    | cons a l ih =>
      convert mul_mem_lowDegree coord (hcoord a) ih using 1
      · simp only [List.length_cons, Nat.add_comm]
      · rfl
  | zero => exact (lowDegree coord d).zero_mem
  | add f g _ _ hf hg => exact (lowDegree coord d).add_mem hf hg
  | smul c f _ hf => exact (lowDegree coord d).smul_mem c hf

lemma weighted_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (L : ℝ) (hL : L ≠ 0) :
    P (origin + dirA) + P (origin + dirB) - P (origin + dirStar) -
      2 * P (origin + dirP) + P origin =
      ∑ g : GridIndex d, weight d L g * P (fun a => origin a + L*(g a:ℝ)) := by
  let Q : Point → ℝ := fun x => P (fun a => origin a + L*x a)
  have hQ : Q ∈ lowDegree coord d := lowDegree_affine_pullback d P hP origin L
  have he (v : Point) : P (origin + v) =
      ∑ g : GridIndex d, (linePolynomial d g v).eval L⁻¹ *
        P (fun a => origin a + L*(g a:ℝ)) := by
    have hi := lowDegree_interpolation d Q hQ (fun a => L⁻¹*v a)
    have hx : (fun a => origin a + L*(L⁻¹*v a)) = origin + v := by
      funext a
      simp [hL]
    simpa only [Q, hx, ← linePolynomial_eval, gridNode] using hi
  have he0 := he 0
  rw [add_zero] at he0
  rw [he dirA, he dirB, he dirStar, he dirP, he0]
  simp only [weight, weightPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    add_mul, sub_mul, mul_assoc, ← Finset.mul_sum]

end MatchingInterpolation

end OAI

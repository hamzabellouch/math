import Mathlib
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq energy_nonneg)
open scoped BigOperators

def MainTarget : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (1/25 : ℝ) * distanceToLaughlinSq ψ ≤ energy ψ

theorem distanceToLaughlinSq_le {N Q : ℕ} (ψ : State N Q) (c : ℂ) :
    distanceToLaughlinSq ψ ≤ ∑ a, ‖ψ a - c * laughlinVector N Q a‖ ^ 2 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨d, rfl⟩
    exact Finset.sum_nonneg (fun a ha => sq_nonneg _)
  · exact ⟨c, rfl⟩

theorem distanceToLaughlinSq_nonneg {N Q : ℕ} (ψ : State N Q) :
    0 ≤ distanceToLaughlinSq ψ := by
  apply le_csInf (Set.range_nonempty _)
  rintro t ⟨c, rfl⟩
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

theorem distanceToLaughlinSq_le_normSq {N Q : ℕ} (ψ : State N Q) :
    distanceToLaughlinSq ψ ≤ ∑ a, ‖ψ a‖ ^ 2 := by
  simpa using distanceToLaughlinSq_le ψ 0

theorem distanceToLaughlinSq_scalar {N Q : ℕ} (c : ℂ) :
    distanceToLaughlinSq (fun a => c * laughlinVector N Q a) = 0 := by
  apply le_antisymm _ (distanceToLaughlinSq_nonneg _)
  simpa using distanceToLaughlinSq_le (fun a => c * laughlinVector N Q a) c

theorem bracket_ne_zero {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    bracket i j ≠ 0 := by
  classical
  intro h
  let f : SpinorVariables N → ℂ := fun x =>
    if x = (i, false) ∨ x = (j, true) then 1 else 0
  have heval := congrArg (MvPolynomial.eval f) h
  have hji : j ≠ i := Ne.symm hij
  simp [bracket, f, hij, hji] at heval

theorem laughlinPolynomial_ne_zero (N : ℕ) : laughlinPolynomial N ≠ 0 := by
  classical
  unfold laughlinPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  split_ifs with h
  · exact pow_ne_zero _ (bracket_ne_zero (ne_of_lt h))
  · exact one_ne_zero

def spinorPermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (SpinorVariables N) :=
  Equiv.prodCongr σ (Equiv.refl Bool)

@[simp]
theorem rename_bracket {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    MvPolynomial.rename (spinorPermutation σ) (bracket i j) = bracket (σ i) (σ j) := by
  simp [bracket, spinorPermutation]

theorem laughlinPolynomial_rename_swap {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.rename (spinorPermutation (Equiv.swap i j)) (laughlinPolynomial N) =
      -laughlinPolynomial N := by
  classical
  unfold laughlinPolynomial
  simp only [map_prod, apply_ite, map_pow, rename_bracket, map_one]
  simp_rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  have ha (i j : Fin N) : bracket i j ^ 3 = -(bracket j i ^ 3) := by
    unfold bracket
    ring
  rw [(Equiv.swap i j).prod_Ioi_comp_eq_sign_mul_prod ha, Equiv.Perm.sign_swap hij]
  simp

theorem monomialExponent_swap {N Q : ℕ} (i j : Fin N) (a : Configuration N Q) :
    monomialExponent (a ∘ Equiv.swap i j) =
      Finsupp.mapDomain (spinorPermutation (Equiv.swap i j)) (monomialExponent a) := by
  ext k
  rw [Finsupp.mapDomain_equiv_apply]
  simp [monomialExponent, spinorPermutation]

theorem laughlinVector_antisymmetric (N Q : ℕ) : Antisymmetric (laughlinVector N Q) := by
  classical
  intro i j hij a
  have hc := MvPolynomial.coeff_rename_mapDomain
    (spinorPermutation (Equiv.swap i j)) (spinorPermutation (Equiv.swap i j)).injective
    (laughlinPolynomial N) (monomialExponent a)
  rw [← monomialExponent_swap, laughlinPolynomial_rename_swap i j hij,
    MvPolynomial.coeff_neg] at hc
  have hden :
      (∏ k : Fin N, Real.sqrt (Nat.choose Q ((a ∘ Equiv.swap i j) k).val : ℝ)) =
      ∏ k : Fin N, Real.sqrt (Nat.choose Q (a k).val : ℝ) :=
    Equiv.prod_comp (Equiv.swap i j) (fun k => Real.sqrt (Nat.choose Q (a k).val : ℝ))
  simp only [laughlinVector, hden]
  rw [← neg_div]
  congr 1
  exact (neg_eq_iff_eq_neg.mp hc)

def particleWeight {N : ℕ} (k : Fin N) : SpinorVariables N → ℕ :=
  fun ib => if ib.1 = k then 1 else 0

theorem particleWeight_eq {N : ℕ} (k : Fin N) (d : SpinorVariables N →₀ ℕ) :
    Finsupp.weight (particleWeight k) d = d (k, false) + d (k, true) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [particleWeight, Fintype.sum_prod_type, mul_ite, Finset.sum_add_distrib, add_comm]

private theorem particle_pair_count {N : ℕ} (k : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0) = N - 1 := by
  classical
  have hterm (i j : Fin N) :
      (if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0 : ℕ) =
      (if i = k then if i < j then 1 else 0 else 0) +
      (if j = k then if i < j then 1 else 0 else 0) := by
    split_ifs <;> simp
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  have hlt (i : Fin N) :
      (if k < i then 1 else 0) + (if i < k then 1 else 0) = (if i = k then 0 else 1 : ℕ) := by
    rcases lt_trichotomy i k with hi | rfl | hi
    · simp [hi, not_lt.mpr (le_of_lt hi), ne_of_lt hi]
    · simp
    · simp [hi, not_lt.mpr (le_of_lt hi), ne_of_gt hi]
  simp_rw [hlt]
  simp [Finset.sum_ite, Finset.filter_ne']

theorem bracket_isWeightedHomogeneous {N : ℕ} (k i j : Fin N) :
    MvPolynomial.IsWeightedHomogeneous (particleWeight k) (bracket i j)
      ((if i = k then 1 else 0) + (if j = k then 1 else 0)) := by
  have h1 := (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (i, false)).mul
    (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (j, true))
  have h2 := (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (j, false)).mul
    (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (particleWeight k) (i, true))
  simp only [particleWeight] at h1 h2
  exact h1.sub (by simpa only [add_comm] using h2)

theorem laughlinPolynomial_isWeightedHomogeneous (N : ℕ) (k : Fin N) :
    MvPolynomial.IsWeightedHomogeneous (particleWeight k) (laughlinPolynomial N) (3 * (N - 1)) := by
  classical
  have hcount : (∑ i : Fin N, ∑ j : Fin N,
      if i < j then 3 * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0) =
      3 * (N - 1) := by
    have hterm (i j : Fin N) :
        (if i < j then 3 * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0) =
        3 * (if i < j then ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0 : ℕ) := by
      split_ifs <;> simp
    simp_rw [hterm, ← Finset.mul_sum]
    rw [particle_pair_count]
  rw [← hcount]
  unfold laughlinPolynomial
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i hi
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro j hj
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using (bracket_isWeightedHomogeneous k i j).pow 3
  · simp only [ite_eq_right hij]
    exact MvPolynomial.isWeightedHomogeneous_one ℂ (particleWeight k)

theorem laughlinPolynomial_support_exponents (N : ℕ) (d : SpinorVariables N →₀ ℕ)
    (hd : (laughlinPolynomial N).coeff d ≠ 0) :
    ∃ a : Configuration N (3 * (N - 1)), monomialExponent a = d := by
  have hdeg (k : Fin N) : d (k, false) + d (k, true) = 3 * (N - 1) := by
    simpa only [particleWeight_eq] using (laughlinPolynomial_isWeightedHomogeneous N k) hd
  let a : Configuration N (3 * (N - 1)) := fun k =>
    ⟨d (k, true), by have h := hdeg k; omega⟩
  refine ⟨a, ?_⟩
  ext ⟨k, b⟩
  cases b
  · simp only [monomialExponent, Finsupp.onFinset_apply, Bool.false_eq_true, ↓reduceIte]
    have h := hdeg k
    change 3 * (N - 1) - d (k, true) = d (k, false)
    omega
  · rfl

theorem laughlinVector_ne_zero (N : ℕ) : laughlinVector N (3 * (N - 1)) ≠ 0 := by
  classical
  have hex : ∃ d, (laughlinPolynomial N).coeff d ≠ 0 := by
    by_contra! h
    apply laughlinPolynomial_ne_zero N
    apply MvPolynomial.ext
    intro d
    simpa using h d
  obtain ⟨d, hd⟩ := hex
  obtain ⟨a, ha⟩ := laughlinPolynomial_support_exponents N d hd
  have hden : (∏ k : Fin N, Real.sqrt ((3 * (N - 1)).choose (a k).val : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a k).isLt)
  intro hzero
  have hz := congrFun hzero a
  have hc : laughlinVector N (3 * (N - 1)) a ≠ 0 := by
    unfold laughlinVector
    rw [ha]
    exact div_ne_zero hd (Complex.ofReal_ne_zero.mpr hden)
  exact hc hz

abbrev TensorHilbert (N Q : ℕ) := EuclideanSpace ℂ (Configuration N Q)

noncomputable def toTensorHilbert {N Q : ℕ} (ψ : State N Q) : TensorHilbert N Q :=
  WithLp.toLp 2 ψ

noncomputable def laughlinLine (N Q : ℕ) : Submodule ℂ (TensorHilbert N Q) :=
  Submodule.span ℂ {toTensorHilbert (laughlinVector N Q)}

noncomputable def laughlinProjection (N Q : ℕ) : TensorHilbert N Q →L[ℂ] TensorHilbert N Q :=
  (laughlinLine N Q).starProjection

@[simp]
theorem toTensorHilbert_apply {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    toTensorHilbert ψ a = ψ a := rfl

@[simp]
theorem toTensorHilbert_norm_sq {N Q : ℕ} (ψ : State N Q) :
    ‖toTensorHilbert ψ‖ ^ 2 = ∑ a, ‖ψ a‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

theorem distanceToLaughlinSq_eq_projection {N Q : ℕ} (ψ : State N Q) :
    distanceToLaughlinSq ψ =
      ‖toTensorHilbert ψ - laughlinProjection N Q (toTensorHilbert ψ)‖ ^ 2 := by
  classical
  let x := toTensorHilbert ψ
  let L := toTensorHilbert (laughlinVector N Q)
  let K := laughlinLine N Q
  have hmem : K.starProjection x ∈ Submodule.span ℂ {L} :=
    K.starProjection_apply_mem x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hnorm (c : ℂ) : ‖x - c • L‖ ^ 2 =
      ∑ a, ‖ψ a - c * laughlinVector N Q a‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  change distanceToLaughlinSq ψ = ‖x - K.starProjection x‖ ^ 2
  apply le_antisymm
  · rw [← hc, hnorm]
    exact distanceToLaughlinSq_le ψ c
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨d, rfl⟩
    change ‖x - K.starProjection x‖ ^ 2 ≤ ∑ a, ‖ψ a - d * laughlinVector N Q a‖ ^ 2
    rw [← hnorm d]
    have hd : d • L ∈ K :=
      Submodule.mem_span_singleton.mpr ⟨d, rfl⟩
    have hmin : ‖x - K.starProjection x‖ ≤ ‖x - d • L‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, fun t ht => by obtain ⟨y, rfl⟩ := ht; positivity⟩
        (⟨d • L, hd⟩ : K)
    exact pow_le_pow_left₀ (norm_nonneg _) hmin 2

theorem distanceToLaughlinSq_eq_quadraticForm {N Q : ℕ} (ψ : State N Q) :
    distanceToLaughlinSq ψ =
      (inner ℂ (toTensorHilbert ψ)
        (toTensorHilbert ψ - laughlinProjection N Q (toTensorHilbert ψ))).re := by
  rw [distanceToLaughlinSq_eq_projection]
  let K := laughlinLine N Q
  let x := toTensorHilbert ψ
  change ‖x - K.starProjection x‖ ^ 2 =
    (inner ℂ x (x - K.starProjection x)).re
  have h := Kᗮ.re_inner_starProjection_eq_normSq x
  change (inner ℂ (Kᗮ.starProjection x) x).re = ‖Kᗮ.starProjection x‖ ^ 2 at h
  rw [Submodule.starProjection_orthogonal_val] at h
  exact h.symm.trans (inner_re_symm (𝕜 := ℂ) _ _)

section PairNormalization
open Polynomial

private noncomputable def euler (P : ℝ[X]) : ℝ[X] := P.derivative * X

private theorem coeff_euler (P : ℝ[X]) (n : ℕ) :
    (euler P).coeff n = (n : ℝ) * P.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]

private theorem weighted_binomial_polynomial_identity (n : ℕ) :
    let F : ℝ[X] := (X + 1) ^ (n + 2)
    euler (euler F) * F + F * euler (euler F) - 2 * (euler F * euler F) =
      C (2 * (n + 2 : ℝ)) * X * (X + 1) ^ (2 * n + 2) := by
  dsimp only
  have hd : ((X + 1) ^ (n + 2) : ℝ[X]).derivative =
      C ((n : ℝ) + 2) * (X + 1) ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, derivative_pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, derivative_add, derivative_X, derivative_one,
      add_zero, mul_one]
    congr 2
    ring
  have hd' : ((X + 1) ^ (n + 1) : ℝ[X]).derivative =
      C ((n : ℝ) + 1) * (X + 1) ^ n := by
    simp [derivative_pow_succ, derivative_add]
  simp only [euler, derivative_mul, hd, derivative_X]
  simp only [derivative_C, hd', zero_mul, zero_add, mul_one]
  simp only [show 2 * n + 2 = n + n + 2 by omega, pow_add, pow_two, map_mul,
    map_add, map_ofNat, map_one]
  ring

theorem weighted_binomial_antidiagonal (Q : ℕ) (hQ : 2 ≤ Q) (p : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p + 1),
      ((ij.1 : ℝ) - ij.2) ^ 2 * (Q.choose ij.1 : ℝ) * Q.choose ij.2) =
      2 * Q * ((2 * Q - 2).choose p : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 2 := ⟨Q - 2, by omega⟩
  have heq : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p + 1),
      ((ij.1 : ℝ) - ij.2) ^ 2 * ((n + 2).choose ij.1 : ℝ) * (n + 2).choose ij.2) =
      ((euler (euler ((X + 1) ^ (n + 2) : ℝ[X]))) * (X + 1) ^ (n + 2) +
        (X + 1) ^ (n + 2) * (euler (euler ((X + 1) ^ (n + 2) : ℝ[X]))) -
        2 * (euler ((X + 1) ^ (n + 2)) * euler ((X + 1) ^ (n + 2)))).coeff (p + 1) := by
    simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_mul, coeff_euler,
      coeff_X_add_one_pow]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [heq, weighted_binomial_polynomial_identity]
  rw [mul_assoc, coeff_C_mul, coeff_X_mul, coeff_X_add_one_pow]
  congr 2
  norm_cast

theorem pairCoefficient_sq (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1)
    (x y : Fin (Q + 1)) :
    pairCoefficient Q p x y ^ 2 =
      if x.val + y.val = p + 1 then
        ((x.val : ℝ) - y.val) ^ 2 * (Q.choose x.val : ℝ) * Q.choose y.val /
          (2 * Q * ((2 * Q - 2).choose p : ℝ))
      else 0 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have hch : ((2 * Q - 2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)).ne'
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) =
      ((Q.choose x.val : ℝ) * Q.choose y.val) /
        ((Q : ℝ) * ((2 * Q - 2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs with hs
  · rw [hrad, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  · simp

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  by_cases hs : x.val + y.val = p + 1
  · simp only [hs, Nat.add_comm y.val x.val, ↓reduceIte]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring
  · simp [hs, Nat.add_comm]

private theorem sum_fin_pair_on_antidiagonal (Q n : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ x y, (Q < x ∨ Q < y) → f x y = 0) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      if x.val + y.val = n then f x.val y.val else 0) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, f ij.1 ij.2 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin (Q + 1),
    if x + y.val = n then f x y.val else 0)]
  have hs (x : ℕ) := Fin.sum_univ_eq_sum_range
    (fun y => if x + y = n then f x y else 0) (Q + 1)
  simp_rw [hs]
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro ij hij
    simpa using (Finset.mem_filter.mp hij).2
  · intro ij hij hnot
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have heq : ij.1 + ij.2 = n := by simpa using hij
    apply hf
    omega

theorem pairCoefficient_sum_sq (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1), pairCoefficient Q p x y ^ 2) = 1 := by
  simp_rw [pairCoefficient_sq Q p hQ hp]
  have hch : ((2 * Q - 2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)).ne'
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  rw [sum_fin_pair_on_antidiagonal Q (p + 1)
    (fun x y => ((x : ℝ) - y) ^ 2 * (Q.choose x : ℝ) * Q.choose y /
      (2 * Q * ((2 * Q - 2).choose p : ℝ)))]
  · rw [← Finset.sum_div, weighted_binomial_antidiagonal Q hQ p]
    field_simp
  · intro x y hxy
    rcases hxy with hx | hy
    · simp [Nat.choose_eq_zero_of_lt hx]
    · simp [Nat.choose_eq_zero_of_lt hy]

theorem pairCoefficient_sum_mul_of_ne (Q p r : ℕ) (hpr : p ≠ r) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      pairCoefficient Q p x y * pairCoefficient Q r x y) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  unfold pairCoefficient
  split_ifs <;> simp_all

abbrev PairHilbert (Q : ℕ) := EuclideanSpace ℂ (Fin (Q + 1) × Fin (Q + 1))

noncomputable def pairVector (Q p : ℕ) : PairHilbert Q :=
  WithLp.toLp 2 (fun xy => (pairCoefficient Q p xy.1 xy.2 : ℂ))

theorem pairVector_inner (Q p r : ℕ) :
    inner ℂ (pairVector Q p) (pairVector Q r) =
      ((∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
        pairCoefficient Q p x y * pairCoefficient Q r x y : ℝ) : ℂ) := by
  simp [pairVector, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

theorem pairVector_orthonormal (Q : ℕ) (hQ : 2 ≤ Q) :
    Orthonormal ℂ (fun p : Fin (2 * Q - 1) => pairVector Q p.val) := by
  rw [orthonormal_iff_ite]
  intro p r
  rw [pairVector_inner]
  split_ifs with hpr
  · subst r
    rw [show (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      pairCoefficient Q p.val x y * pairCoefficient Q p.val x y) = 1 by
        simpa only [pow_two] using pairCoefficient_sum_sq Q p.val hQ p.isLt]
    rfl
  · rw [pairCoefficient_sum_mul_of_ne Q p.val r.val (fun h => hpr (Fin.ext h))]
    rfl

noncomputable def pairChannel (Q : ℕ) : Submodule ℂ (PairHilbert Q) :=
  Submodule.span ℂ (Set.range (fun p : Fin (2 * Q - 1) => pairVector Q p.val))

private theorem projection_span_orthonormal_eq_sum
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] (v : ι → E) (hv : Orthonormal ℂ v) (x : E) :
    (Submodule.span ℂ (Set.range v)).starProjection x =
      ∑ p, inner ℂ (v p) x • v p := by
  classical
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨p, rfl⟩ := hw
      rw [inner_sub_left, hv.inner_left_fintype, inner_conj_symm]
      simp
    | zero => simp
    | add u v hu hv ihu ihv => simp [inner_add_right, ihu, ihv]
    | smul a w hw ih => simp [inner_smul_right, ih]

theorem pairChannel_projection_eq (Q : ℕ) (hQ : 2 ≤ Q) (x : PairHilbert Q) :
    (pairChannel Q).starProjection x =
      ∑ p : Fin (2 * Q - 1), inner ℂ (pairVector Q p.val) x • pairVector Q p.val :=
  projection_span_orthonormal_eq_sum _ (pairVector_orthonormal Q hQ) x

theorem pairChannel_projection_norm_sq (Q : ℕ) (hQ : 2 ≤ Q) (x : PairHilbert Q) :
    ‖(pairChannel Q).starProjection x‖ ^ 2 =
      ∑ p : Fin (2 * Q - 1), ‖inner ℂ (pairVector Q p.val) x‖ ^ 2 := by
  rw [pairChannel_projection_eq Q hQ]
  rw [@norm_sq_eq_re_inner ℂ]
  rw [(pairVector_orthonormal Q hQ).inner_sum]
  change (∑ p : Fin (2 * Q - 1),
    (starRingEnd ℂ) (inner ℂ (pairVector Q p.val) x) * inner ℂ (pairVector Q p.val) x).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end PairNormalization

noncomputable def pairSlice {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (a : Configuration N Q) : PairHilbert Q :=
  WithLp.toLp 2 (fun xy => ψ (Function.update (Function.update a i xy.1) j xy.2))

theorem pairAmplitude_eq_inner {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (p : ℕ) (a : Configuration N Q) :
    pairAmplitude ψ i j p a = inner ℂ (pairVector Q p) (pairSlice ψ i j a) := by
  simp [pairAmplitude, pairSlice, pairVector, PiLp.inner_apply, Fintype.sum_prod_type,
    mul_comm]

theorem energy_eq_sum_pair_projections {N Q : ℕ} (hQ : 2 ≤ Q) (ψ : State N Q) :
    energy ψ = ∑ i : Fin N, ∑ j : Fin N, if i < j then
      ∑ a : Configuration N Q, if a i = 0 ∧ a j = 0 then
        ‖(pairChannel Q).starProjection (pairSlice ψ i j a)‖ ^ 2 else 0
      else 0 := by
  classical
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hij
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hanchor : a i = 0 ∧ a j = 0
    · simp only [hanchor, and_self, ↓reduceIte]
      rw [pairChannel_projection_norm_sq Q hQ]
      rw [Fin.sum_univ_eq_sum_range
        (fun p : ℕ => ‖inner ℂ (pairVector Q p) (pairSlice ψ i j a)‖ ^ 2)]
      simp_rw [pairAmplitude_eq_inner]
    · simp [hanchor]
  · rfl

theorem kernel_distance_of_square_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (γ : ℝ) (hsq : ∀ x : E, γ * (inner ℂ x (T x)).re ≤ ‖T x‖ ^ 2)
    (x : E) :
    ∃ y : E, T y = 0 ∧ γ * ‖x - y‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis rfl
  let lam := hT.isSymmetric.eigenvalues rfl
  have hdiag (v : E) (i : Fin (Module.finrank ℂ E)) :
      b.repr (T v) i = (lam i : ℂ) * b.repr v i :=
    hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
  have hlambda (i : Fin (Module.finrank ℂ E)) : lam i = 0 ∨ γ ≤ lam i := by
    by_cases hi : lam i = 0
    · exact Or.inl hi
    right
    have hnonneg : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
    have h := hsq (b i)
    have heig : T (b i) = (lam i : ℂ) • b i :=
      hT.isSymmetric.apply_eigenvectorBasis rfl i
    rw [heig, inner_smul_right, b.inner_eq_one, mul_one] at h
    simp only [Complex.ofReal_re, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      b.norm_eq_one, mul_one, sq_abs] at h
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using h) (lt_of_le_of_ne hnonneg (Ne.symm hi))
  let c : EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    WithLp.toLp 2 (fun i => if lam i = 0 then b.repr x i else 0)
  let y := b.repr.symm c
  have hyrepr : b.repr y = c := b.repr.apply_symm_apply c
  have hTy : T y = 0 := by
    apply b.repr.injective
    ext i
    rw [hdiag, hyrepr, map_zero]
    change (lam i : ℂ) * (if lam i = 0 then b.repr x i else 0) = 0
    split_ifs with hi <;> simp [hi]
  have henergy : (inner ℂ x (T x)).re = ∑ i, lam i * ‖b.repr x i‖ ^ 2 := by
    rw [← b.repr.inner_map_map, PiLp.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiag, RCLike.inner_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  refine ⟨y, hTy, ?_⟩
  rw [henergy, ← b.repr.norm_map (x - y), EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [map_sub, hyrepr, PiLp.sub_apply]
  change γ * ‖b.repr x i - (if lam i = 0 then b.repr x i else 0)‖ ^ 2 ≤ _
  obtain hzero | hge := hlambda i
  · simp [hzero]
  · by_cases hzero : lam i = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte, sub_zero]
      exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)

theorem kernel_projection_bound_of_square_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsq : ∀ x : E, γ * (inner ℂ x (T x)).re ≤ ‖T x‖ ^ 2)
    (x : E) :
    γ * ‖x - (LinearMap.ker T).starProjection x‖ ^ 2 ≤
      (inner ℂ x (T x)).re := by
  obtain ⟨y, hy, hbound⟩ := kernel_distance_of_square_lower_bound T hT γ hsq x
  have hmin : ‖x - (LinearMap.ker T).starProjection x‖ ≤ ‖x - y‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun t ht => by obtain ⟨z, rfl⟩ := ht; positivity⟩
      (⟨y, hy⟩ : LinearMap.ker T)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hmin 2) hγ).trans
    hbound

theorem orthonormal_rows_coordinate_sq_le
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (S : ι → EuclideanSpace ℂ κ) (hS : Orthonormal ℂ S) (A : κ → τ → ℂ) :
    (∑ r, ∑ a, ‖∑ b, star (S r b) * A b a‖ ^ 2) ≤
      ∑ b, ∑ a, ‖A b a‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ r, ‖∑ b, star (S r b) * A b a‖ ^ 2) ≤
        ∑ a, ∑ b, ‖A b a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      let v : EuclideanSpace ℂ κ := WithLp.toLp 2 (fun b => A b a)
      have h := hS.sum_inner_products_le (s := Finset.univ) v
      simpa [PiLp.inner_apply, RCLike.inner_apply', EuclideanSpace.norm_sq_eq, v, mul_comm] using h
    _ = ∑ b, ∑ a, ‖A b a‖ ^ 2 := Finset.sum_comm

theorem orthonormal_rows_sq_le
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (S : ι → EuclideanSpace ℂ κ) (hS : Orthonormal ℂ S)
    (A : κ → EuclideanSpace ℂ τ) :
    (∑ r, ‖∑ b, star (S r b) • A b‖ ^ 2) ≤ ∑ b, ‖A b‖ ^ 2 := by
  simpa [EuclideanSpace.norm_sq_eq, WithLp.ofLp_sum, Finset.sum_apply]
    using orthonormal_rows_coordinate_sq_le S hS (fun b a => A b a)

def OrbitalTriple (D : ℕ) :=
  {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + t.2.2 = D ∧ t.2.1 < t.2.2}

def orbitalTripleEquiv (D : ℕ) :
    (Σ n : Fin (D + 1), Fin ((n.val + 1) / 2)) ≃ OrbitalTriple D where
  toFun a := ⟨(D - a.1.val, a.2.val, a.1.val - a.2.val), by
    have hn := a.1.isLt
    have hj := a.2.isLt
    constructor <;> dsimp only <;> omega⟩
  invFun t := ⟨⟨t.val.2.1 + t.val.2.2, by have h := t.property; omega⟩,
    ⟨t.val.2.1, by have h := t.property; dsimp only; omega⟩⟩
  left_inv a := by
    have hn := a.1.isLt
    have hj := a.2.isLt
    have he : a.2.val + (a.1.val - a.2.val) = a.1.val := by omega
    apply Sigma.ext
    · exact Fin.ext he
    · exact (Fin.heq_ext_iff (congrArg (fun n => (n + 1) / 2) he)).mpr rfl
  right_inv t := by
    have h := t.property
    apply Subtype.ext
    apply Prod.ext
    · simp only
      omega
    · apply Prod.ext
      · rfl
      · simp only
        omega

noncomputable instance (D : ℕ) : Fintype (OrbitalTriple D) :=
  Fintype.ofEquiv _ (orbitalTripleEquiv D)

theorem orbitalTriple_card (D : ℕ) :
    Fintype.card (OrbitalTriple D) =
      ∑ n ∈ Finset.range (D + 1), (n + 1) / 2 := by
  rw [← Fintype.card_congr (orbitalTripleEquiv D), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => (n + 1) / 2) (D + 1)

theorem retained_orbitalTriple_count :
    (∑ D ∈ Finset.Icc 1 23, Fintype.card (OrbitalTriple D)) = 1222 := by
  simp_rw [orbitalTriple_card]
  norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ]

noncomputable def gammaStar : ℝ := 4616733319001 / 10 ^ 14

theorem final_margin_arithmetic :
    (1 : ℝ) - 93527408868499 / 10 ^ 14 - 61 / 4096 -
      1222 * (3 / 10 ^ 6) = gammaStar := by
  norm_num [gammaStar]

theorem one_div_twenty_five_lt_gammaStar : (1 / 25 : ℝ) < gammaStar := by
  norm_num [gammaStar]

theorem bracket_irreducible {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Irreducible (bracket i j) := by
  classical
  let d₁ : SpinorVariables N →₀ ℕ := Finsupp.single (i, false) 1 + Finsupp.single (j, true) 1
  let d₂ : SpinorVariables N →₀ ℕ := Finsupp.single (j, false) 1 + Finsupp.single (i, true) 1
  have h₁ : d₁ (i, false) = 1 := by simp [d₁]
  have h₂ : d₂ (i, false) = 0 := by simp [d₂, hij]
  have hne : d₁ ≠ d₂ := by intro he; have := congrFun (congrArg DFunLike.coe he) (i, false); omega
  have heq : bracket i j = MvPolynomial.monomial d₁ (1 : ℂ) + MvPolynomial.monomial d₂ (-1 : ℂ) := by
    simp [bracket, d₁, d₂, MvPolynomial.X, sub_eq_add_neg]
  have hcoeff (d) : (bracket i j).coeff d = (if d₁ = d then 1 else 0) +
      (if d₂ = d then -1 else 0) := by
    by_cases h : d₂ = d <;> simp [heq, MvPolynomial.coeff_monomial, h]
  have hsupp : (bracket i j).support = {d₁, d₂} := by
    ext d
    simp only [MvPolynomial.mem_support_iff, hcoeff, Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne d d₁ with rfl | h₁
    · simp [hne.symm]
    rcases eq_or_ne d d₂ with rfl | h₂
    · simp [hne]
    simp [h₁, h₂, h₁.symm, h₂.symm]
  apply MvPolynomial.irreducible_of_disjoint_support
  · exact ⟨d₁, by simp [hsupp], d₂, by simp [hsupp], hne⟩
  · rw [hsupp]; exact Finset.mem_insert_self ..
  · exact h₁
  · rw [hsupp]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hd : Disjoint d₁.support d₂.support := by
      simp [d₁, d₂, Finsupp.support_add_eq, hij, Ne.symm hij]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hab rfl).elim
  · intro r hr
    apply isUnit_of_dvd_one
    simpa [hcoeff, hne, Ne.symm hne] using hr d₁

theorem bracket_not_dvd {N : ℕ} {i j k l : Fin N} (hij : i < j) (hkl : k < l)
    (hne : (i, j) ≠ (k, l)) : ¬bracket k l ∣ bracket i j := by
  classical
  have hex : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) := by
    by_contra! h
    have hi : i = k ∨ i = l := by tauto
    have hj : j = k ∨ j = l := by tauto
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (lt_irrefl _ hij)
    · exact hne rfl
    · exact (not_lt_of_ge (le_of_lt hkl) hij)
    · exact (lt_irrefl _ hij)
  let f (m : Fin N) : SpinorVariables N → ℂ := fun ib =>
    if ib.2 then (if ib.1 = m then 0 else 1) else (if ib.1 = m then 1 else 0)
  intro hdiv
  obtain ⟨g, hg⟩ := hdiv
  rcases hex with hi | hj
  · have h := congrArg (MvPolynomial.eval (f i)) hg
    simp [bracket, f, Ne.symm hi.1, Ne.symm hi.2, (ne_of_lt hij).symm] at h
  · have h := congrArg (MvPolynomial.eval (f j)) hg
    simp [bracket, f, Ne.symm hj.1, Ne.symm hj.2, ne_of_lt hij] at h

theorem laughlinPolynomial_dvd_of_bracket_cubes_dvd {N : ℕ}
    (F : MvPolynomial (SpinorVariables N) ℂ)
    (h : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ F) :
    laughlinPolynomial N ∣ F := by
  classical
  have heq : laughlinPolynomial N =
      ∏ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
        bracket ij.1 ij.2 ^ 3 := by
    simp only [Finset.prod_filter, Fintype.prod_prod_type, laughlinPolynomial]
  rw [heq]
  apply Finset.prod_dvd_of_isRelPrime
  · intro ij hij kl hkl hne
    have hij' := (Finset.mem_filter.mp hij).2
    have hkl' := (Finset.mem_filter.mp hkl).2
    exact ((bracket_irreducible (ne_of_lt hij')).isRelPrime_iff_not_dvd.mpr
      (bracket_not_dvd hkl' hij' hne.symm)).pow
  · intro ij hij
    exact h ij.1 ij.2 (Finset.mem_filter.mp hij).2

theorem isHomogeneous_of_particle_homogeneous {N Q : ℕ}
    (F : MvPolynomial (SpinorVariables N) ℂ)
    (h : ∀ k : Fin N, MvPolynomial.IsWeightedHomogeneous (particleWeight k) F Q) :
    F.IsHomogeneous (N * Q) := by
  classical
  intro d hd
  have hdeg (k : Fin N) : d (k, false) + d (k, true) = Q := by
    simpa only [particleWeight_eq] using h k hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, add_comm (d (_, true)), hdeg]
  simp

theorem laughlinPolynomial_totalDegree (N : ℕ) :
    (laughlinPolynomial N).totalDegree = N * (3 * (N - 1)) :=
  (isHomogeneous_of_particle_homogeneous _
    (laughlinPolynomial_isWeightedHomogeneous N)).totalDegree (laughlinPolynomial_ne_zero N)

theorem eq_scalar_laughlin_of_bracket_cubes_dvd {N : ℕ}
    (F : MvPolynomial (SpinorVariables N) ℂ)
    (hdeg : ∀ k : Fin N,
      MvPolynomial.IsWeightedHomogeneous (particleWeight k) F (3 * (N - 1)))
    (hdiv : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ F) :
    ∃ c : ℂ, F = c • laughlinPolynomial N := by
  obtain ⟨G, hG⟩ := laughlinPolynomial_dvd_of_bracket_cubes_dvd F hdiv
  by_cases hG0 : G = 0
  · refine ⟨0, ?_⟩
    simp [hG, hG0]
  have htd := (isHomogeneous_of_particle_homogeneous F hdeg).totalDegree_le
  rw [hG, MvPolynomial.totalDegree_mul_of_isDomain (laughlinPolynomial_ne_zero N) hG0,
    laughlinPolynomial_totalDegree] at htd
  have hzero : G.totalDegree = 0 := by omega
  refine ⟨G.coeff 0, ?_⟩
  rw [hG, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hzero, mul_comm,
    MvPolynomial.C_mul']
  simp

noncomputable def tensorMonomialScale {N Q : ℕ} (a : Configuration N Q) : ℝ :=
  ∏ i : Fin N, Real.sqrt (Nat.choose Q (a i).val : ℝ)

theorem tensorMonomialScale_pos {N Q : ℕ} (a : Configuration N Q) :
    0 < tensorMonomialScale a := by
  unfold tensorMonomialScale
  exact Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)))

noncomputable def statePolynomial {N Q : ℕ} (ψ : State N Q) :
    MvPolynomial (SpinorVariables N) ℂ :=
  ∑ a : Configuration N Q, MvPolynomial.monomial (monomialExponent a)
    ((tensorMonomialScale a : ℂ) * ψ a)

theorem monomialExponent_injective (N Q : ℕ) :
    Function.Injective (monomialExponent (N := N) (Q := Q)) := by
  intro a b he
  funext k
  apply Fin.ext
  have h := congrArg (fun d : SpinorVariables N →₀ ℕ => d (k, true)) he
  simpa only [monomialExponent, Finsupp.onFinset_apply, ↓reduceIte] using h

@[simp]
theorem coeff_statePolynomial {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (statePolynomial ψ).coeff (monomialExponent a) = (tensorMonomialScale a : ℂ) * ψ a := by
  classical
  simp [statePolynomial, MvPolynomial.coeff_monomial, (monomialExponent_injective N Q).eq_iff]

theorem coeff_statePolynomial_of_not_grid {N Q : ℕ} (ψ : State N Q)
    (d : SpinorVariables N →₀ ℕ) (h : ∀ a : Configuration N Q, monomialExponent a ≠ d) :
    (statePolynomial ψ).coeff d = 0 := by
  classical
  simp [statePolynomial, MvPolynomial.coeff_monomial, h]

theorem statePolynomial_injective (N Q : ℕ) :
    Function.Injective (statePolynomial (N := N) (Q := Q)) := by
  intro ψ φ h
  funext a
  have ha := congrArg (fun F : MvPolynomial (SpinorVariables N) ℂ =>
    F.coeff (monomialExponent a)) h
  simp only [coeff_statePolynomial] at ha
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (tensorMonomialScale_pos a))) ha

theorem statePolynomial_isWeightedHomogeneous {N Q : ℕ} (ψ : State N Q) (k : Fin N) :
    MvPolynomial.IsWeightedHomogeneous (particleWeight k) (statePolynomial ψ) Q := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro a ha
  apply MvPolynomial.isWeightedHomogeneous_monomial
  rw [particleWeight_eq]
  simp only [monomialExponent, Finsupp.onFinset_apply, Bool.false_eq_true, ↓reduceIte]
  exact Nat.sub_add_cancel (Nat.le_of_lt_succ (a k).isLt)

@[simp]
theorem statePolynomial_smul {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    statePolynomial (c • ψ) = c • statePolynomial ψ := by
  classical
  unfold statePolynomial
  simp only [Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← MvPolynomial.C_mul']
  simp only [MvPolynomial.C_mul_monomial]
  congr 1
  ring

@[simp]
theorem statePolynomial_laughlinVector (N : ℕ) :
    statePolynomial (laughlinVector N (3 * (N - 1))) = laughlinPolynomial N := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : ∃ a : Configuration N (3 * (N - 1)), monomialExponent a = d
  · obtain ⟨a, rfl⟩ := hd
    rw [coeff_statePolynomial]
    change (tensorMonomialScale a : ℂ) *
      ((laughlinPolynomial N).coeff (monomialExponent a) / (tensorMonomialScale a : ℂ)) = _
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (tensorMonomialScale_pos a)))
  · push Not at hd
    rw [coeff_statePolynomial_of_not_grid _ _ hd]
    by_contra hc
    obtain ⟨a, ha⟩ := laughlinPolynomial_support_exponents N d (Ne.symm hc)
    exact hd a ha

theorem state_eq_scalar_laughlin_of_bracket_cubes_dvd {N : ℕ}
    (ψ : State N (3 * (N - 1)))
    (h : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ statePolynomial ψ) :
    ∃ c : ℂ, ψ = c • laughlinVector N (3 * (N - 1)) := by
  obtain ⟨c, hc⟩ := eq_scalar_laughlin_of_bracket_cubes_dvd (statePolynomial ψ)
    (statePolynomial_isWeightedHomogeneous ψ) h
  refine ⟨c, (statePolynomial_injective _ _).eq_iff.mp ?_⟩
  simpa only [statePolynomial_smul, statePolynomial_laughlinVector] using hc

theorem pairAmplitude_eq_of_spectators_eq {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (p : ℕ) (a b : Configuration N Q)
    (h : ∀ k, k ≠ i → k ≠ j → a k = b k) :
    pairAmplitude ψ i j p a = pairAmplitude ψ i j p b := by
  classical
  unfold pairAmplitude
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  congr 2
  funext k
  by_cases hkj : k = j
  · simp [hkj]
  by_cases hki : k = i
  · simp [Function.update_apply, hki]
  simp [hki, hkj, h k hki hkj]

theorem pairAmplitude_anchor {N Q : ℕ} (ψ : State N Q) (i j : Fin N)
    (p : ℕ) (a : Configuration N Q) :
    pairAmplitude ψ i j p (Function.update (Function.update a i 0) j 0) =
      pairAmplitude ψ i j p a := by
  apply pairAmplitude_eq_of_spectators_eq
  intro k hki hkj
  simp [hki, hkj]

theorem energy_eq_zero_iff {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ i j : Fin N, i < j → ∀ p : ℕ, p < 2 * Q - 1 →
      ∀ a : Configuration N Q, pairAmplitude ψ i j p a = 0 := by
  classical
  constructor
  · intro h i j hij p hp a
    unfold energy at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp h i
      (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hi j
      (Finset.mem_univ j)
    rw [ite_eq_left hij] at hj
    have hpp := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hj p
      (Finset.mem_range.mpr hp)
    let b := Function.update (Function.update a i 0) j 0
    have hb : b i = 0 ∧ b j = 0 := by
      simp [b, ne_of_lt hij]
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (by intro _ _; positivity)).mp hpp b
      (Finset.mem_univ b)
    rw [ite_eq_left hb] at ha
    rw [pairAmplitude_anchor] at ha
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ha)
  · intro h
    unfold energy
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with hij
    · apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro a ha
      simp [h i j hij p (Finset.mem_range.mp hp) a]
    · rfl

def antisymmetricSubmodule (N Q : ℕ) : Submodule ℂ (TensorHilbert N Q) where
  carrier := {ψ | Antisymmetric (WithLp.ofLp ψ)}
  zero_mem' := by intros i j hij a; simp
  add_mem' := by
    intro ψ φ hψ hφ i j hij a
    change ψ (a ∘ Equiv.swap i j) + φ (a ∘ Equiv.swap i j) = -(ψ a + φ a)
    rw [hψ i j hij a, hφ i j hij a, neg_add]
  smul_mem' := by
    intro c ψ hψ i j hij a
    change c * ψ (a ∘ Equiv.swap i j) = -(c * ψ a)
    rw [hψ i j hij a, mul_neg]

abbrev SectorHilbert (N Q : ℕ) := ↥(antisymmetricSubmodule N Q)

abbrev ContractionIndex (N Q : ℕ) :=
  Fin N × Fin N × Fin (2 * Q - 1) × Configuration N Q

noncomputable def pairContractions (N Q : ℕ) :
    TensorHilbert N Q →ₗ[ℂ] EuclideanSpace ℂ (ContractionIndex N Q) where
  toFun ψ := WithLp.toLp 2 (fun t =>
    if t.1 < t.2.1 ∧ t.2.2.2 t.1 = 0 ∧ t.2.2.2 t.2.1 = 0 then
      pairAmplitude (WithLp.ofLp ψ) t.1 t.2.1 t.2.2.1.val t.2.2.2 else 0)
  map_add' := by
    intro ψ φ
    ext t
    change (if _ then pairAmplitude _ _ _ _ _ else _) =
      (if _ then pairAmplitude _ _ _ _ _ else _) + (if _ then pairAmplitude _ _ _ _ _ else _)
    split_ifs
    · simp [pairAmplitude, mul_add, Finset.sum_add_distrib]
    · simp
  map_smul' := by
    intro c ψ
    ext t
    change (if _ then pairAmplitude _ _ _ _ _ else _) =
      c * (if _ then pairAmplitude _ _ _ _ _ else _)
    split_ifs
    · simp [pairAmplitude, Finset.mul_sum, mul_left_comm]
    · simp

theorem pairContractions_norm_sq {N Q : ℕ} (ψ : TensorHilbert N Q) :
    ‖pairContractions N Q ψ‖ ^ 2 = energy (WithLp.ofLp ψ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [pairContractions, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, true_and, ↓reduceIte]
    rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
      ∑ a : Configuration N Q,
        ‖if a i = 0 ∧ a j = 0 then pairAmplitude (WithLp.ofLp ψ) i j p a else 0‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  · simp [hij]

noncomputable def sectorContractions (N Q : ℕ) :
    SectorHilbert N Q →ₗ[ℂ] EuclideanSpace ℂ (ContractionIndex N Q) :=
  (pairContractions N Q).comp (antisymmetricSubmodule N Q).subtype

noncomputable def sectorHamiltonian (N Q : ℕ) :
    SectorHilbert N Q →ₗ[ℂ] SectorHilbert N Q :=
  (LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)).comp (sectorContractions N Q)

theorem sectorHamiltonian_positive (N Q : ℕ) : LinearMap.IsPositive (𝕜 := ℂ) (E := SectorHilbert N Q) (sectorHamiltonian N Q) :=
  LinearMap.isPositive_adjoint_comp_self (𝕜 := ℂ)
    (E := SectorHilbert N Q) (F := EuclideanSpace ℂ (ContractionIndex N Q)) _

theorem sectorHamiltonian_inner {N Q : ℕ} (ψ : SectorHilbert N Q) :
    (inner ℂ ψ (sectorHamiltonian N Q ψ)).re = energy (WithLp.ofLp ψ.val) := by
  change (inner ℂ ψ ((LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)) (sectorContractions N Q ψ))).re = _
  rw [LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (sectorContractions N Q ψ)).symm.trans
    (pairContractions_norm_sq ψ.val)

theorem sectorHamiltonian_eq_zero_iff {N Q : ℕ} (ψ : SectorHilbert N Q) :
    sectorHamiltonian N Q ψ = 0 ↔ energy (WithLp.ofLp ψ.val) = 0 := by
  constructor
  · intro h
    rw [← sectorHamiltonian_inner ψ, h]
    simp
  · intro h
    have ha : sectorContractions N Q ψ = 0 := by
      apply norm_eq_zero.mp
      have hnorm : ‖sectorContractions N Q ψ‖ ^ 2 = 0 :=
        (pairContractions_norm_sq ψ.val).trans h
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm
    change (LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)) (sectorContractions N Q ψ) = 0
    rw [ha, map_zero]

namespace Chart
open MvPolynomial
open scoped BigOperators

noncomputable def difference {σ : Type*} (i j : σ) : MvPolynomial σ ℂ := X j - X i

noncomputable def diagonal {σ : Type*} [DecidableEq σ] (i j : σ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ := rename (Function.update id j i)

theorem difference_dvd_sub_diagonal {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) : difference i j ∣ F - diagonal i j F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [diagonal]
  | add a b ha hb => simpa only [map_add, add_sub_add_comm] using dvd_add ha hb
  | mul_X p k hp =>
    have hx : difference i j ∣ X k - diagonal i j (X k) := by
      by_cases hk : k = j
      · simp [hk, diagonal, difference]
      · simp [diagonal, hk]
    have hd := dvd_add (dvd_mul_of_dvd_left hp (X k))
      (dvd_mul_of_dvd_right hx (diagonal i j p))
    convert hd using 1
    simp only [map_mul]
    ring

theorem difference_dvd_of_diagonal_eq_zero {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) (h : diagonal i j F = 0) : difference i j ∣ F := by
  simpa only [h, sub_zero] using difference_dvd_sub_diagonal i j F

lemma difference_ne_zero {σ : Type*} {i j : σ} (h : i ≠ j) : difference i j ≠ 0 := by
  classical
  intro he
  have hh := congrArg (MvPolynomial.eval (fun k : σ => if k = j then (1 : ℂ) else 0)) he
  simp [difference, h] at hh

@[simp]
lemma diagonal_difference {σ : Type*} [DecidableEq σ] (i j : σ) :
    diagonal i j (difference i j) = 0 := by
  by_cases h : i = j
  · simp [difference, h]
  · simp [diagonal, difference, h]

lemma diagonal_rename_swap {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) :
    diagonal i j (rename (Equiv.swap i j) F) = diagonal i j F := by
  unfold diagonal
  rw [rename_rename]
  have he : Function.update id j i ∘ Equiv.swap i j = Function.update id j i := by
    funext k
    by_cases hki : k = i
    · subst k; by_cases hij : i = j <;> simp [hij]
    by_cases hkj : k = j
    · subst k; simp [Ne.symm hki]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hkj]
  rw [he]

theorem diagonal_eq_zero_of_antisymmetric {σ : Type*} [DecidableEq σ] (i j : σ)
    (F : MvPolynomial σ ℂ) (h : rename (Equiv.swap i j) F = -F) :
    diagonal i j F = 0 := by
  have hd := congrArg (diagonal i j) h
  rw [diagonal_rename_swap, map_neg] at hd
  have hs : (2 : ℂ) • diagonal i j F = 0 := by
    rw [two_smul]
    calc
      diagonal i j F + diagonal i j F = -diagonal i j F + diagonal i j F :=
        congrArg (fun x => x + diagonal i j F) hd
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

lemma rename_difference_swap {σ : Type*} [DecidableEq σ] (i j : σ) :
    rename (Equiv.swap i j) (difference i j) = -difference i j := by
  simp [difference, sub_eq_add_neg]

theorem difference_cube_dvd {σ : Type*} [DecidableEq σ] (i j : σ) (hij : i ≠ j)
    (F : MvPolynomial σ ℂ) (hanti : rename (Equiv.swap i j) F = -F)
    (hderiv : diagonal i j (pderiv j F) = 0) : difference i j ^ 3 ∣ F := by
  obtain ⟨G, hG⟩ := difference_dvd_of_diagonal_eq_zero i j F
    (diagonal_eq_zero_of_antisymmetric i j F hanti)
  have hGsym : rename (Equiv.swap i j) G = G := by
    rw [hG, map_mul, rename_difference_swap, neg_mul] at hanti
    exact mul_left_cancel₀ (difference_ne_zero hij) (neg_inj.mp hanti)
  have hdiagG : diagonal i j G = 0 := by
    rw [hG, pderiv_mul] at hderiv
    simpa [difference, diagonal, hij, Ne.symm hij] using hderiv
  obtain ⟨H, hH⟩ := difference_dvd_of_diagonal_eq_zero i j G hdiagG
  have hHanti : rename (Equiv.swap i j) H = -H := by
    rw [hH, map_mul, rename_difference_swap, neg_mul] at hGsym
    apply mul_left_cancel₀ (difference_ne_zero hij)
    simpa only [mul_neg] using neg_eq_iff_eq_neg.mp hGsym
  obtain ⟨K, hK⟩ := difference_dvd_of_diagonal_eq_zero i j H
    (diagonal_eq_zero_of_antisymmetric i j H hHanti)
  refine ⟨K, ?_⟩
  rw [hG, hH, hK]
  ring

end Chart

section LocalKernel
open MvPolynomial

noncomputable def pairWeightScale (Q p : ℕ) : ℝ :=
  Real.sqrt (1 / ((Q : ℝ) * (2 * Q - 2).choose p)) / Real.sqrt 2

theorem pairWeightScale_pos {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1) :
    0 < pairWeightScale Q p := by
  unfold pairWeightScale
  have hc : (0 : ℝ) < ((2 * Q - 2).choose p : ℝ) := by
    exact_mod_cast Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)
  positivity

theorem pairCoefficient_binomial (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p x y =
      if x.val + y.val = p + 1 then
        pairWeightScale Q p * ((x.val : ℝ) - y.val) *
          (Real.sqrt (Q.choose x.val : ℝ) * Real.sqrt (Q.choose y.val : ℝ))
      else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) =
      ((Q.choose x.val : ℝ) * Q.choose y.val) *
        (1 / ((Q : ℝ) * ((2 * Q - 2).choose p : ℝ))) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs
  · rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    unfold pairWeightScale
    ring
  · rfl

noncomputable def pairMoment {Q : ℕ} (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) (n : ℕ) : ℂ :=
  ∑ x, ∑ y, if x.val + y.val = n then
    ((x.val : ℂ) - y.val) *
      ((Real.sqrt (Q.choose x.val : ℝ) * Real.sqrt (Q.choose y.val : ℝ) : ℝ) : ℂ) * φ x y
    else 0

theorem pair_contraction_eq_moment {Q p : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y) =
      (pairWeightScale Q p : ℂ) * pairMoment φ (p + 1) := by
  simp only [pairMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [pairCoefficient_binomial]
  split_ifs
  · push_cast
    ring
  · simp

noncomputable def localPairPolynomial {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) : MvPolynomial Bool ℂ :=
  ∑ x, ∑ y, C (((Real.sqrt (Q.choose x.val : ℝ) * Real.sqrt (Q.choose y.val : ℝ) : ℝ) : ℂ) * φ x y) *
    X false ^ x.val * X true ^ y.val

theorem localPairPolynomial_antisymmetric {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) (hφ : ∀ x y, φ y x = -φ x y) :
    rename (Equiv.swap false true) (localPairPolynomial φ) = - localPairPolynomial φ := by
  classical
  simp only [localPairPolynomial, map_sum, map_mul, map_pow, rename_C, rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hφ x y]
  simp only [mul_neg, map_neg, neg_mul]
  push_cast
  ring_nf

private theorem diagonal_difference_derivative_monomial (x y : ℕ) (c : ℂ) :
    Chart.diagonal false true
      (pderiv false (C c * X false ^ x * X true ^ y) -
        pderiv true (C c * X false ^ x * X true ^ y)) =
      C (((x : ℂ) - y) * c) * X false ^ (x + y - 1) := by
  simp only [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne (by decide : true ≠ false), pderiv_X_of_ne (by decide : false ≠ true)]
  cases x <;> cases y <;> simp [Chart.diagonal, pow_add, pow_succ] <;> ring_nf

theorem pairMoment_eq_zero_of_contractions {Q : ℕ} (hQ : 2 ≤ Q)
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (h : ∀ p < 2 * Q - 1, ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y = 0)
    (n : ℕ) : pairMoment φ n = 0 := by
  by_cases hn : 0 < n ∧ n < 2 * Q
  · have hp : n - 1 < 2 * Q - 1 := by omega
    have he := h (n - 1) hp
    rw [pair_contraction_eq_moment, Nat.sub_add_cancel hn.1] at he
    exact (mul_eq_zero.mp he).resolve_left
      (Complex.ofReal_ne_zero.mpr (pairWeightScale_pos hQ hp).ne')
  · unfold pairMoment
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    split_ifs with hxy
    · have he : x.val = y.val := by have := x.isLt; have := y.isLt; omega
      simp [he]
    · rfl

theorem localPairPolynomial_diagonal_difference_derivative {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Chart.diagonal false true
      (pderiv false (localPairPolynomial φ) - pderiv true (localPairPolynomial φ)) =
    ∑ n ∈ Finset.range (2 * Q + 1), C (pairMoment φ n) * X false ^ (n - 1) := by
  classical
  simp only [localPairPolynomial, map_sum, ← Finset.sum_sub_distrib,
    diagonal_difference_derivative_monomial]
  simp only [pairMoment, map_sum, Finset.sum_mul, apply_ite C, map_zero, ite_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  symm
  rw [Finset.sum_eq_single (x.val + y.val)]
  · simp [mul_assoc]
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by have := x.isLt; have := y.isLt; omega))).elim

theorem localPairPolynomial_cubic_divisibility {Q : ℕ} (hQ : 2 ≤ Q)
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (hanti : ∀ x y, φ y x = -φ x y)
    (hker : ∀ p < 2 * Q - 1, ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y = 0) :
    Chart.difference false true ^ 3 ∣ localPairPolynomial φ := by
  have ha := localPairPolynomial_antisymmetric φ hanti
  apply Chart.difference_cube_dvd false true (by decide) _ ha
  have hd : Chart.diagonal false true
      (pderiv false (localPairPolynomial φ) - pderiv true (localPairPolynomial φ)) = 0 := by
    rw [localPairPolynomial_diagonal_difference_derivative]
    simp [pairMoment_eq_zero_of_contractions hQ φ hker]
  have hs := pderiv_rename (Equiv.swap false true).injective false (localPairPolynomial φ)
  simp only [Equiv.swap_apply_left, ha, map_neg] at hs
  have hds := congrArg (Chart.diagonal false true) hs
  rw [map_neg, Chart.diagonal_rename_swap] at hds
  rw [map_sub] at hd
  have hz : (2 : MvPolynomial Bool ℂ) *
      Chart.diagonal false true (pderiv true (localPairPolynomial φ)) = 0 := by
    linear_combination -hd - hds
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end LocalKernel

namespace Chart
open MvPolynomial

noncomputable def spinorChart (N : ℕ) :
    MvPolynomial (SpinorVariables N) ℂ →ₐ[ℂ] MvPolynomial (Fin N) ℂ :=
  aeval (fun ib => if ib.2 then X ib.1 else 1)

noncomputable def exponent {N Q : ℕ} (a : Configuration N Q) : Fin N →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => (a i).val) (by intro; simp)

noncomputable def statePolynomial {N Q : ℕ} (ψ : State N Q) : MvPolynomial (Fin N) ℂ :=
  ∑ a : Configuration N Q, monomial (exponent a) ((tensorMonomialScale a : ℂ) * ψ a)

noncomputable def laughlinPolynomial (N : ℕ) : MvPolynomial (Fin N) ℂ :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then difference i j ^ 3 else 1

lemma monomial_as_prod {N Q : ℕ} (a : Configuration N Q) (c : ℂ) :
    monomial (exponent a) c = C c * ∏ i : Fin N, X i ^ (a i).val := by
  rw [monomial_eq, Finsupp.prod_pow]
  rfl

lemma exponent_injective (N Q : ℕ) : Function.Injective (exponent (N := N) (Q := Q)) := by
  intro a b h
  funext k
  apply Fin.ext
  exact congrArg (fun d : Fin N →₀ ℕ => d k) h

@[simp] theorem coeff_statePolynomial {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (statePolynomial ψ).coeff (exponent a) = (tensorMonomialScale a : ℂ) * ψ a := by
  classical
  simp [statePolynomial, coeff_monomial, (exponent_injective N Q).eq_iff]

theorem statePolynomial_injective (N Q : ℕ) :
    Function.Injective (statePolynomial (N := N) (Q := Q)) := by
  intro ψ φ h
  funext a
  have ha := congrArg (fun F : MvPolynomial (Fin N) ℂ => F.coeff (exponent a)) h
  simp only [coeff_statePolynomial] at ha
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (tensorMonomialScale_pos a).ne') ha

@[simp] theorem statePolynomial_smul {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    statePolynomial (c • ψ) = c • statePolynomial ψ := by
  classical
  unfold statePolynomial
  simp only [Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← C_mul']
  simp only [C_mul_monomial]
  congr 1
  ring

theorem spinorChart_statePolynomial {N Q : ℕ} (ψ : State N Q) :
    spinorChart N (LaughlinGap.statePolynomial ψ) = statePolynomial ψ := by
  classical
  simp only [LaughlinGap.statePolynomial, map_sum, statePolynomial]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [spinorChart, aeval_monomial]
  simp [Fintype.prod_prod_type, LaughlinGap.monomialExponent, monomial_as_prod]

@[simp] theorem spinorChart_bracket {N : ℕ} (i j : Fin N) :
    spinorChart N (bracket i j) = difference i j := by
  simp [spinorChart, bracket, difference]

@[simp] theorem spinorChart_laughlinPolynomial (N : ℕ) :
    spinorChart N (LaughlinGap.laughlinPolynomial N) = laughlinPolynomial N := by
  classical
  simp [LaughlinGap.laughlinPolynomial, laughlinPolynomial, apply_ite]

@[simp] theorem statePolynomial_laughlinVector (N : ℕ) :
    statePolynomial (laughlinVector N (3 * (N - 1))) = laughlinPolynomial N := by
  rw [← spinorChart_statePolynomial, LaughlinGap.statePolynomial_laughlinVector,
    spinorChart_laughlinPolynomial]

theorem statePolynomial_degreeOf_le {N Q : ℕ} (ψ : State N Q) (k : Fin N) :
    (statePolynomial ψ).degreeOf k ≤ Q := by
  classical
  apply degreeOf_le_iff.mpr
  intro d hd
  have hex : ∃ a : Configuration N Q, exponent a = d := by
    by_contra! h
    have hz : (statePolynomial ψ).coeff d = 0 := by
      simp [statePolynomial, coeff_monomial, h]
    exact (mem_support_iff.mp hd) hz
  obtain ⟨a, rfl⟩ := hex
  exact Nat.le_of_lt_succ (a k).isLt

abbrev PairSpectators {N Q : ℕ} (i j : Fin N) :=
  {a : Configuration N Q // a i = 0 ∧ a j = 0}

def pairConfigurationEquiv {N Q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Configuration N Q ≃ PairSpectators (Q := Q) i j × Fin (Q + 1) × Fin (Q + 1) where
  toFun a := (⟨Function.update (Function.update a i 0) j 0, by simp [hij]⟩, a i, a j)
  invFun t := Function.update (Function.update t.1.val i t.2.1) j t.2.2
  left_inv a := by
    funext k
    by_cases hkj : k = j
    · simp [hkj]
    by_cases hki : k = i
    · simp [hki, hij]
    simp [Function.update_of_ne hkj, Function.update_of_ne hki]
  right_inv t := by
    rcases t with ⟨⟨a, ha⟩, x, y⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hkj : k = j
      · simp [hkj, ha.2]
      by_cases hki : k = i
      · simp [hki, hij, ha.1]
      simp [Function.update_of_ne hkj, Function.update_of_ne hki]
    · simp [hij]

private lemma prod_update_pair {N Q : ℕ} {M : Type*} [CommMonoid M]
    (i j : Fin N) (hij : i ≠ j) (a : Configuration N Q) (x y : Fin (Q + 1))
    (f : Fin N → Fin (Q + 1) → M) :
    (∏ k : Fin N, f k (Function.update (Function.update a i x) j y k)) =
      f i x * f j y * ∏ k ∈ (Finset.univ.erase i).erase j, f k (a k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
  simp only [Function.update_of_ne hij, Function.update_self, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  have hi := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hj := (Finset.mem_erase.mp hk).1
  simp [Function.update_of_ne hi, Function.update_of_ne hj]

private lemma monomial_as_normalized_prod {N Q : ℕ} (a : Configuration N Q) (c : ℂ) :
    monomial (exponent a) ((tensorMonomialScale a : ℂ) * c) =
      C c * ∏ k : Fin N, C (Real.sqrt (Q.choose (a k).val : ℝ) : ℂ) * X k ^ (a k).val := by
  rw [monomial_as_prod]
  simp only [tensorMonomialScale, Complex.ofReal_prod, map_mul, map_prod, Finset.prod_mul_distrib]
  ring

noncomputable def spectatorMonomial {N Q : ℕ} (i j : Fin N)
    (a : PairSpectators (Q := Q) i j) : MvPolynomial (Fin N) ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j,
    C (Real.sqrt (Q.choose (a.val k).val : ℝ) : ℂ) * X k ^ (a.val k).val

theorem statePolynomial_pair_decomposition {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    statePolynomial ψ =
      ∑ a : PairSpectators (Q := Q) i j, spectatorMonomial i j a *
        rename (fun b : Bool => if b then j else i)
          (localPairPolynomial (fun x y => ψ (Function.update (Function.update a.val i x) j y))) := by
  classical
  unfold statePolynomial
  rw [← (pairConfigurationEquiv (Q := Q) i j hij).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [localPairPolynomial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  change monomial (exponent (Function.update (Function.update a.val i x) j y))
    ((tensorMonomialScale (Function.update (Function.update a.val i x) j y) : ℂ) *
      ψ (Function.update (Function.update a.val i x) j y)) = _
  rw [monomial_as_normalized_prod, prod_update_pair i j hij a.val x y
    (fun k x => C (Real.sqrt (Q.choose x.val : ℝ) : ℂ) * X k ^ x.val)]
  simp only [map_mul, map_pow, rename_C, rename_X, Bool.false_eq_true, ↓reduceIte,
    Complex.ofReal_mul]
  unfold spectatorMonomial
  ring

private lemma update_pair_swap {N Q : ℕ} (a : Configuration N Q)
    (i j : Fin N) (hij : i ≠ j) (x y : Fin (Q + 1)) :
    (Function.update (Function.update a i x) j y) ∘ Equiv.swap i j =
      Function.update (Function.update a i y) j x := by
  funext k
  by_cases hki : k = i
  · simp [hki, hij]
  by_cases hkj : k = j
  · simp [hkj, hij]
  simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj,
    Function.update_of_ne hki, Function.update_of_ne hkj]

theorem difference_cube_dvd_statePolynomial_of_energy_zero {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) (hE : energy ψ = 0)
    (i j : Fin N) (hij : i < j) : difference i j ^ 3 ∣ statePolynomial ψ := by
  classical
  rw [statePolynomial_pair_decomposition ψ i j (ne_of_lt hij)]
  apply Finset.dvd_sum
  intro a ha
  apply dvd_mul_of_dvd_right
  have hlocal := localPairPolynomial_cubic_divisibility hQ
    (fun x y => ψ (Function.update (Function.update a.val i x) j y))
    (by
      intro x y
      have h := hψ i j (ne_of_lt hij) (Function.update (Function.update a.val i x) j y)
      rwa [update_pair_swap a.val i j (ne_of_lt hij)] at h)
    (fun p hp => (LaughlinGap.energy_eq_zero_iff ψ).mp hE i j hij p hp a.val)
  have hd := map_dvd (rename (fun b : Bool => if b then j else i)).toRingHom hlocal
  simpa [difference] using hd

theorem difference_irreducible {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Irreducible (difference i j) := by
  have ht : (difference i j).totalDegree = 1 :=
    ((isHomogeneous_X ℂ j).sub (isHomogeneous_X ℂ i)).totalDegree (difference_ne_zero hij)
  apply irreducible_of_totalDegree_eq_one ht
  intro r hr
  apply isUnit_of_dvd_one
  have hs : Finsupp.single i 1 ≠ (Finsupp.single j 1 : Fin N →₀ ℕ) := by
    intro h
    have hc := congrArg (fun d : Fin N →₀ ℕ => d i) h
    simp [hij] at hc
  simpa [difference, coeff_X, hs] using hr (Finsupp.single j 1)

theorem difference_not_dvd {N : ℕ} {i j k l : Fin N} (hij : i < j) (hkl : k < l)
    (hne : (i, j) ≠ (k, l)) : ¬ difference k l ∣ difference i j := by
  have hex : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) := by
    by_contra! h
    have hi : i = k ∨ i = l := by tauto
    have hj : j = k ∨ j = l := by tauto
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (lt_irrefl _ hij)
    · exact hne rfl
    · exact (not_lt_of_ge (le_of_lt hkl) hij)
    · exact (lt_irrefl _ hij)
  intro hdiv
  obtain ⟨g, hg⟩ := hdiv
  rcases hex with hi | hj
  · have h := congrArg (eval (fun m : Fin N => if m = i then (1 : ℂ) else 0)) hg
    simp [difference, Ne.symm hi.1, Ne.symm hi.2, (ne_of_lt hij).symm] at h
  · have h := congrArg (eval (fun m : Fin N => if m = j then (1 : ℂ) else 0)) hg
    simp [difference, Ne.symm hj.1, Ne.symm hj.2, ne_of_lt hij] at h

theorem laughlinPolynomial_ne_zero (N : ℕ) : laughlinPolynomial N ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  split_ifs with hij
  · exact pow_ne_zero _ (difference_ne_zero (ne_of_lt hij))
  · exact one_ne_zero

theorem laughlinPolynomial_dvd_of_difference_cubes_dvd {N : ℕ}
    (F : MvPolynomial (Fin N) ℂ) (h : ∀ i j : Fin N, i < j → difference i j ^ 3 ∣ F) :
    laughlinPolynomial N ∣ F := by
  classical
  have heq : laughlinPolynomial N =
      ∏ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
        difference ij.1 ij.2 ^ 3 := by
    simp only [Finset.prod_filter, Fintype.prod_prod_type, laughlinPolynomial]
  rw [heq]
  apply Finset.prod_dvd_of_isRelPrime
  · intro ij hij kl hkl hne
    have hij' := (Finset.mem_filter.mp hij).2
    have hkl' := (Finset.mem_filter.mp hkl).2
    exact ((difference_irreducible (ne_of_lt hij')).isRelPrime_iff_not_dvd.mpr
      (difference_not_dvd hkl' hij' hne.symm)).pow
  · intro ij hij
    exact h ij.1 ij.2 (Finset.mem_filter.mp hij).2

lemma difference_degreeOf {N : ℕ} (i j k : Fin N) (hij : i ≠ j) :
    (difference i j).degreeOf k = (if i = k then 1 else 0) + (if j = k then 1 else 0) := by
  by_cases hki : k = i
  · subst k
    have hd := degreeOf_add_eq_of_degreeOf_lt
      (p := -(X i : MvPolynomial (Fin N) ℂ)) (q := X j) (i := i)
      (by simp [degreeOf_X, hij])
    simpa [difference, sub_eq_add_neg, add_comm, Ne.symm hij] using hd
  by_cases hkj : k = j
  · subst k
    have hd := degreeOf_add_eq_of_degreeOf_lt
      (p := (X j : MvPolynomial (Fin N) ℂ)) (q := -X i) (i := j)
      (by simp [degreeOf_X, Ne.symm hij])
    simpa [difference, sub_eq_add_neg, hij] using hd
  have hd := degreeOf_sub_le k (X j : MvPolynomial (Fin N) ℂ) (X i)
  have hz : (difference i j).degreeOf k = 0 := by
    simpa [difference, degreeOf_X, hkj, hki] using hd
  simpa [Ne.symm hki, Ne.symm hkj] using hz

theorem laughlinPolynomial_degreeOf (N : ℕ) (k : Fin N) :
    (laughlinPolynomial N).degreeOf k = 3 * (N - 1) := by
  classical
  have hf (i j : Fin N) : (if i < j then difference i j ^ 3 else 1) ≠ 0 := by
    split_ifs with hij
    · exact pow_ne_zero _ (difference_ne_zero (ne_of_lt hij))
    · exact one_ne_zero
  have hterm (i j : Fin N) :
      degreeOf k (if i < j then difference i j ^ 3 else 1) =
      3 * (if i < j then (if i = k then 1 else 0) + (if j = k then 1 else 0) else 0) := by
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      rw [degreeOf_pow_eq _ _ _ (difference_ne_zero (ne_of_lt hij)), difference_degreeOf _ _ _ (ne_of_lt hij)]
    · simp [hij]
  unfold laughlinPolynomial
  rw [degreeOf_prod_eq _ _ (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hf i j))]
  simp_rw [degreeOf_prod_eq _ _ (fun j _ => hf _ j), hterm, ← Finset.mul_sum]
  rw [LaughlinGap.particle_pair_count]

private lemma eq_constant_of_degreeOf_eq_zero {N : ℕ} (G : MvPolynomial (Fin N) ℂ)
    (h : ∀ k, G.degreeOf k = 0) : G = C (G.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · simp [hd]
  have hz : G.coeff d = 0 := by
    by_contra hc
    have hde : d = 0 := by
      apply Finsupp.ext
      intro k
      have hk := monomial_le_degreeOf k (mem_support_iff.mpr hc)
      rw [h k] at hk
      exact Nat.eq_zero_of_le_zero hk
    exact hd hde
  simp [hz, coeff_C, Ne.symm hd]

theorem eq_scalar_laughlin_of_difference_cubes_dvd {N : ℕ}
    (F : MvPolynomial (Fin N) ℂ) (hdeg : ∀ k : Fin N, F.degreeOf k ≤ 3 * (N - 1))
    (hdiv : ∀ i j : Fin N, i < j → difference i j ^ 3 ∣ F) :
    ∃ c : ℂ, F = c • laughlinPolynomial N := by
  obtain ⟨G, hG⟩ := laughlinPolynomial_dvd_of_difference_cubes_dvd F hdiv
  by_cases hG0 : G = 0
  · refine ⟨0, ?_⟩
    simp [hG, hG0]
  have hz : ∀ k : Fin N, G.degreeOf k = 0 := by
    intro k
    have hd := hdeg k
    rw [hG, degreeOf_mul_eq (laughlinPolynomial_ne_zero N) hG0, laughlinPolynomial_degreeOf] at hd
    omega
  refine ⟨G.coeff 0, ?_⟩
  rw [hG, eq_constant_of_degreeOf_eq_zero G hz, mul_comm, C_mul']
  simp

end Chart

theorem energy_zero_imp_laughlin {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3 * (N - 1))) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∃ c : ℂ, ψ = c • laughlinVector N (3 * (N - 1)) := by
  obtain ⟨c, hc⟩ := Chart.eq_scalar_laughlin_of_difference_cubes_dvd
    (Chart.statePolynomial ψ) (Chart.statePolynomial_degreeOf_le ψ)
    (Chart.difference_cube_dvd_statePolynomial_of_energy_zero (by omega) ψ hψ hE)
  refine ⟨c, (Chart.statePolynomial_injective _ _).eq_iff.mp ?_⟩
  simpa only [Chart.statePolynomial_smul, Chart.statePolynomial_laughlinVector] using hc

theorem laughlin_gap_of_sector_square_estimate {N : ℕ} (hN : 2 ≤ N)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsq : ∀ x : SectorHilbert N (3 * (N - 1)),
      γ * energy (WithLp.ofLp x.val) ≤ ‖sectorHamiltonian N (3 * (N - 1)) x‖ ^ 2)
    (ψ : State N (3 * (N - 1))) (hψ : Antisymmetric ψ) :
    γ * distanceToLaughlinSq ψ ≤ energy ψ := by
  let x : SectorHilbert N (3 * (N - 1)) := ⟨toTensorHilbert ψ, hψ⟩
  obtain ⟨y, hy, hb⟩ := kernel_distance_of_square_lower_bound
    (sectorHamiltonian N (3 * (N - 1))) (sectorHamiltonian_positive _ _) γ
    (fun z => by rw [sectorHamiltonian_inner]; exact hsq z) x
  have hyE : energy (WithLp.ofLp y.val) = 0 := (sectorHamiltonian_eq_zero_iff y).mp hy
  obtain ⟨c, hc⟩ := energy_zero_imp_laughlin hN (WithLp.ofLp y.val) y.property hyE
  have hycoord (a) : y.val a = c * laughlinVector N (3 * (N - 1)) a :=
    congrFun hc a
  have hn : ‖x - y‖ ^ 2 = ∑ a, ‖ψ a - c * laughlinVector N (3 * (N - 1)) a‖ ^ 2 := by
    change ‖toTensorHilbert ψ - y.val‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a ha
    change ‖ψ a - y.val a‖ ^ 2 = _
    rw [hycoord a]
  rw [sectorHamiltonian_inner, hn] at hb
  exact (mul_le_mul_of_nonneg_left (distanceToLaughlinSq_le ψ c) hγ).trans hb

theorem mainTarget_of_uniform_sector_square_estimate
    (h : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∀ N : ℕ, N ≤ Q + 1 →
      ∀ x : SectorHilbert N Q, (1 / 25 : ℝ) * energy (WithLp.ofLp x.val) ≤ ‖sectorHamiltonian N Q x‖ ^ 2) :
    MainTarget := by
  obtain ⟨Q₀, hQ₀⟩ := h
  refine ⟨Q₀ + 2, by omega, ?_⟩
  intro N hN ψ hψ
  exact laughlin_gap_of_sector_square_estimate (by omega) (1 / 25) (by norm_num)
    (hQ₀ _ (by omega) N (by omega)) ψ hψ

end LaughlinGap

end

end OAI

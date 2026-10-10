import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LagrangeBounds01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial

namespace RoughInterpolation

def Integral (x : ℚ) : Prop := ∃ z : ℤ, (z : ℚ) = x

lemma primitive_linear {a b : ℤ} (h : IsCoprime a b) :
    (C a + C b * X).IsPrimitive := by
  intro d hd
  have hc := (C_dvd_iff_dvd_coeff d (C a + C b * X)).mp hd
  exact h.isUnit_of_dvd' (by simpa using hc 0) (by simpa only [coeff_add, coeff_C, coeff_C_mul, coeff_X,
    one_ne_zero, ↓reduceIte, mul_one, zero_add] using hc 1)

lemma primitive_pow {p : ℤ[X]} (hp : p.IsPrimitive) (e : ℕ) :
    (p ^ e).IsPrimitive := by
  induction e with
  | zero => simp
  | succ e he => simpa [pow_succ] using he.mul hp

 
theorem integral_scaled_quotient {a b D : ℤ} (hab : IsCoprime a b)
    (e : ℕ) {R M : ℚ[X]}
    (hR : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ))
    (hdiv : R = (C (a : ℚ) + C (b : ℚ) * X) ^ e * M) :
    C (D : ℚ) * M ∈ lifts (algebraMap ℤ ℚ) := by
  apply (primitive_pow (primitive_linear hab) e).map_mul_mem_lifts_iff.mp
  simpa [hdiv, mul_assoc, mul_left_comm, mul_comm] using hR

 
theorem integral_of_coprime_multiples {a b : ℤ} (hab : IsCoprime a b) {x : ℚ}
    (ha : Integral ((a : ℚ) * x)) (hb : Integral ((b : ℚ) * x)) : Integral x := by
  obtain ⟨u, v, huv⟩ := hab
  obtain ⟨y, hy⟩ := ha
  obtain ⟨z, hz⟩ := hb
  refine ⟨u * y + v * z, ?_⟩
  push_cast
  rw [hy, hz]
  have huv' : (u : ℚ) * a + (v : ℚ) * b = 1 := by exact_mod_cast huv
  linear_combination huv' * x

lemma integral_eval_of_lifts {p : ℚ[X]} (hp : p ∈ lifts (algebraMap ℤ ℚ)) (z : ℤ) :
    Integral (p.eval (z : ℚ)) := by
  obtain ⟨p, rfl⟩ := (mem_lifts _).mp hp
  exact ⟨p.eval z, by simp⟩

 
theorem quotient_integral_at {a b D z : ℤ} (hab : IsCoprime a b)
    (hDz : IsCoprime D (a + b * z)) (e : ℕ) {R M : ℚ[X]}
    (hR : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ))
    (hz : Integral (R.eval (z : ℚ)))
    (hdiv : R = (C (a : ℚ) + C (b : ℚ) * X) ^ e * M) :
    Integral (M.eval (z : ℚ)) := by
  have hMD := integral_eval_of_lifts (integral_scaled_quotient hab e hR hdiv) z
  have hMt : Integral (((a + b * z : ℤ) : ℚ) ^ e * M.eval (z : ℚ)) := by
    simpa [hdiv] using hz
  apply integral_of_coprime_multiples hDz.pow_right
  · simpa using hMD
  · simpa using hMt

 
lemma integral_rational_eval {p : ℚ[X]} (hp : p ∈ lifts (algebraMap ℤ ℚ))
    {q : ℕ} (hq : p.natDegree ≤ q) (a b : ℤ) (hb : b ≠ 0) :
    Integral (p.eval ((a : ℚ) / b) * (b : ℚ) ^ q) := by
  obtain ⟨P, rfl⟩ := (mem_lifts _).mp hp
  refine ⟨MvPolynomial.eval ![a, b] (P.homogenize q), ?_⟩
  have heq := eval_homogenize hq ![(a : ℚ), (b : ℚ)] (by simpa using hb)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at heq
  rw [← heq, homogenize_map]
  change (algebraMap ℤ ℚ) (MvPolynomial.eval ![a, b] (P.homogenize q)) = _
  rw [MvPolynomial.map_eval]
  have hv : (algebraMap ℤ ℚ) ∘ ![a, b] = ![(a : ℚ), (b : ℚ)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

lemma lifts_iterate_derivative {p : ℚ[X]} (hp : p ∈ lifts (algebraMap ℤ ℚ)) (j : ℕ) :
    derivative^[j] p ∈ lifts (algebraMap ℤ ℚ) := by
  obtain ⟨P, rfl⟩ := (mem_lifts _).mp hp
  exact (mem_lifts _).mpr ⟨derivative^[j] P, (iterate_derivative_map _ _ _).symm⟩

 
lemma derivative_rational_denominator {R : ℚ[X]} {D a b : ℤ} {q : ℕ}
    (hR : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ))
    (hq : R.natDegree ≤ q) (hb : b ≠ 0) (j : ℕ) :
    Integral ((D : ℚ) * (b : ℚ) ^ q *
      (derivative^[j] R).eval ((a : ℚ) / b)) := by
  have h := integral_rational_eval (lifts_iterate_derivative hR j)
    ((natDegree_iterate_derivative _ _).trans
      ((Nat.sub_le _ _).trans ((natDegree_C_mul_le _ _).trans hq))) a b hb
  rw [iterate_derivative_C_mul, eval_mul, eval_C] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

 
lemma integral_eq_zero_of_abs_lt_one {x : ℚ} (hx : Integral x) (hsmall : |x| < 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  have hz : |z| < 1 := by exact_mod_cast hsmall
  have : z = 0 := by
    by_contra h
    have := Int.one_le_abs h
    omega
  simp [this]

 
theorem derivative_eq_zero_of_small {R : ℚ[X]} {D a b : ℤ} {q : ℕ}
    (hR : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ))
    (hq : R.natDegree ≤ q) (hD : D ≠ 0) (hb : b ≠ 0) (j : ℕ)
    (hsmall : |(derivative^[j] R).eval ((a : ℚ) / b)| <
      1 / (|(D : ℚ)| * |(b : ℚ)| ^ q)) :
    (derivative^[j] R).eval ((a : ℚ) / b) = 0 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hpos : 0 < |(D : ℚ)| * |(b : ℚ)| ^ q := by positivity
  have hz := integral_eq_zero_of_abs_lt_one (derivative_rational_denominator hR hq hb j)
    (show |(D : ℚ) * (b : ℚ) ^ q * (derivative^[j] R).eval ((a : ℚ) / b)| < 1 by
      rw [abs_mul, abs_mul, abs_pow, mul_comm]
      exact (lt_div_iff₀ hpos).mp hsmall)
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hDq (pow_ne_zero _ hbq))

 
theorem exact_linear_division {R : ℚ[X]} {a b : ℚ} (hb : b ≠ 0) {e : ℕ}
    (hzero : ∀ j < e, (derivative^[j] R).eval (-a / b) = 0) :
    ∃ M : ℚ[X], R = (C a + C b * X) ^ e * M := by
  have hroot : (X - C (-a / b)) ^ e ∣ R := by
    by_cases hR : R = 0
    · simp [hR]
    by_cases he : e = 0
    · simp [he]
    apply (le_rootMultiplicity_iff hR).mp
    have h := lt_rootMultiplicity_of_isRoot_iterate_derivative hR
      (n := e - 1) (fun j hj => hzero j (by omega))
    omega
  obtain ⟨M, hM⟩ := hroot
  refine ⟨C (b⁻¹ ^ e) * M, ?_⟩
  rw [hM]
  have heq : C a + C b * X = C b * (X - C (-a / b)) := by
    rw [mul_sub, ← map_mul]
    have ht : b * (-a / b) = -a := by field_simp
    rw [ht, map_neg]
    ring
  rw [heq, mul_pow]
  have hunit : (C b : ℚ[X]) ^ e * C (b⁻¹ ^ e) = 1 := by
    rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hb, one_pow, map_one]
  calc
    _ = ((C b) ^ e * C (b⁻¹ ^ e)) * ((X - C (-a / b)) ^ e * M) := by
      rw [hunit, one_mul]
    _ = _ := by ring

 
lemma linear_power_derivative_zero {F : Type*} [Field F] {a b : F} (hb : b ≠ 0)
    (θ : F[X]) {e j : ℕ} (hj : j < e) :
    (derivative^[j] ((C a + C b * X) ^ e * θ)).eval (-a / b) = 0 := by
  have hd : (C a + C b * X) ^ (e - j) ∣
      derivative^[j] ((C a + C b * X) ^ e * θ) :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd j (dvd_mul_right _ _)
  obtain ⟨P, hP⟩ := hd
  rw [hP, eval_mul, eval_pow, eval_add, eval_C, eval_mul, eval_C, eval_X]
  have hz : a + b * (-a / b) = 0 := by field_simp; ring
  rw [hz, zero_pow (by omega : e - j ≠ 0), zero_mul]

 
lemma integral_eq_of_near {D : ℤ} (hD : D ≠ 0) {x : ℚ}
    (hx : Integral ((D : ℚ) * x)) (n : ℤ)
    (hnear : |x - (n : ℚ)| < 1 / |(D : ℚ)|) : x = n := by
  obtain ⟨m, hm⟩ := hx
  have hint : Integral ((D : ℚ) * (x - n)) := by
    refine ⟨m - D * n, ?_⟩
    push_cast
    rw [hm]
    ring
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hz := integral_eq_zero_of_abs_lt_one hint
    (show |(D : ℚ) * (x - n)| < 1 by
      rw [abs_mul, mul_comm]
      exact (lt_div_iff₀ (abs_pos.mpr hDq)).mp hnear)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hDq)

end RoughInterpolation

 

noncomputable section
namespace ExactInterpolation
open LagrangeBounds RoughInterpolation

def uniformConstant (q : ℕ) : ℝ := (q + 1 : ℝ) * (2 * q) ^ q

def derivativeConstant (N q : ℕ) : ℝ := 1 + ∑ j ∈ range q,
  ∑ i : Fin (q + 1), coefficientBound
    (derivative^[j] (Lagrange.basis univ (fun i => (nodes N q i : ℝ)) i)) q

lemma derivativeConstant_pos (N q : ℕ) : 0 < derivativeConstant N q := by
  have : 0 ≤ ∑ j ∈ range q, ∑ i : Fin (q + 1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (nodes N q i : ℝ)) i)) q :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => coefficientBound_nonneg _ _))
  unfold derivativeConstant
  linarith

lemma derivative_sum_le {N q j : ℕ} (hj : j < q) :
    (∑ i : Fin (q + 1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (nodes N q i : ℝ)) i)) q) ≤
        derivativeConstant N q := by
  have h := single_le_sum (s := range q)
    (f := fun j => ∑ i : Fin (q + 1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (nodes N q i : ℝ)) i)) q)
    (fun _ _ => sum_nonneg (fun _ _ => coefficientBound_nonneg _ _)) (mem_range.mpr hj)
  unfold derivativeConstant
  linarith

lemma quotient_degree {a b : ℚ} (hb : b ≠ 0) {e q : ℕ} {R M : ℚ[X]}
    (hR : R.natDegree ≤ q) (hdiv : R = (C a + C b * X) ^ e * M) :
    M.natDegree ≤ q - e := by
  by_cases hM : M = 0
  · simp [hM]
  have hlin : (C a + C b * X).natDegree = 1 := by
    rw [natDegree_add_eq_right_of_natDegree_lt (by simp [natDegree_C_mul_X b hb]),
      natDegree_C_mul_X b hb]
  have hne : C a + C b * X ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hlin
    omega
  rw [hdiv, natDegree_mul (pow_ne_zero _ hne) hM, natDegree_pow, hlin, mul_one] at hR
  omega

 

theorem quantitative_exact_division {N q : ℕ} (hq : 0 < q) (hN : 2 * q ≤ N) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (a b : ℤ) (e : ℕ) (θ : ℝ[X]) (ε : ℝ),
      b ≠ 0 → IsCoprime a b → e ≤ q → 0 ≤ ε →
      ((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).natDegree ≤ q →
      (∀ z : ℤ, 0 ≤ z → z ≤ N → ∃ n : ℤ,
        |((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).eval (z : ℝ) - (n : ℝ)| ≤ ε) →
      (∀ z : ℤ, 0 ≤ z → z ≤ N → IsCoprime D (a + b * z)) →
      (uniformConstant q + 1) * ε < 1 / |(D : ℝ)| →
      ε * derivativeConstant N q * (1 + |-(a : ℝ) / b|) ^ q <
        1 / (|(D : ℝ)| * |(b : ℝ)| ^ q) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        C (D : ℚ) * M ∈ lifts (algebraMap ℤ ℚ) ∧
        (∀ z : ℤ, 0 ≤ z → z ≤ N → Integral (M.eval (z : ℚ))) ∧
        ∀ x : ℝ, x ∈ Set.Icc 0 (N : ℝ) →
          |((M.map (algebraMap ℚ ℝ)).eval x - θ.eval x) * ((a : ℝ) + b * x) ^ e| ≤
            uniformConstant q * ε := by
  obtain ⟨D, hD, hden⟩ := interpolation_common_denominator
    (univ : Finset (Fin (q + 1))) (fun i => (nodes N q i : ℚ))
  refine ⟨D, hD, ?_⟩
  intro a b e θ ε hb hab he hε hT hnear hcop hsmall hderiv
  let T : ℝ[X] := (C (a : ℝ) + C (b : ℝ) * X) ^ e * θ
  have hnear' : ∀ i : Fin (q + 1), ∃ n : ℤ, |T.eval (nodes N q i : ℝ) - n| ≤ ε := by
    intro i
    have hi := nodes_mem (N := N) i
    exact hnear (nodes N q i) (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  choose r hr using hnear'
  let R : ℚ[X] := Lagrange.interpolate univ (fun i => (nodes N q i : ℚ)) (fun i => (r i : ℚ))
  have hRlifts : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ) := hden r
  have hinj : Function.Injective (fun i : Fin (q + 1) => (nodes N q i : ℚ)) := by
    intro i j hij
    apply nodes_injective hq hN
    change (nodes N q i : ℚ) = nodes N q j at hij
    have hz : nodes N q i = nodes N q j := by exact_mod_cast hij
    change (nodes N q i : ℝ) = nodes N q j
    exact_mod_cast hz
  have hRdeg : R.natDegree ≤ q := by
    apply natDegree_le_of_degree_le
    have h := Lagrange.degree_interpolate_le (s := univ) (fun i => (r i : ℚ)) hinj.injOn
    simpa only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] using h
  have hRmap : R.map (algebraMap ℚ ℝ) =
      Lagrange.interpolate univ (fun i => (nodes N q i : ℝ)) (fun i => (r i : ℝ)) := by
    change (Lagrange.interpolate univ (fun i => (nodes N q i : ℚ)) (fun i => (r i : ℚ))).map _ = _
    rw [map_interpolate]
    simp only [map_intCast]
  have herr (x : ℝ) (hx : x ∈ Set.Icc 0 (N : ℝ)) :
      |(R.map (algebraMap ℚ ℝ)).eval x - T.eval x| ≤ uniformConstant q * ε := by
    rw [hRmap]
    apply uniform_integer_interpolation hq hN T hT _ hε _ hx
    intro i
    simpa only [abs_sub_comm] using hr i
  have hzero : ∀ j < e, (derivative^[j] R).eval (-(a : ℚ) / b) = 0 := by
    intro j hj
    apply derivative_eq_zero_of_small (a := -a) hRlifts hRdeg hD hb j
    have hTd : T.degree < ((univ : Finset (Fin (q + 1))).card : WithBot ℕ) := by
      simp only [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (degree_le_natDegree.trans (show (T.natDegree : WithBot ℕ) ≤ (q : WithBot ℕ) by exact_mod_cast hT))
        (by exact_mod_cast Nat.lt_succ_self q)
    have h := derivative_interpolation_error univ (fun i => (nodes N q i : ℝ))
      (nodes_injective hq hN).injOn (q := q) (by simp) T hTd (fun i => (r i : ℝ))
      hε (fun i _ => by simpa only [abs_sub_comm] using hr i) j (-(a : ℝ) / b)
    rw [← hRmap, iterate_derivative_sub, eval_sub,
      linear_power_derivative_zero (by exact_mod_cast hb) θ hj, sub_zero] at h
    have h' : |(derivative^[j] (R.map (algebraMap ℚ ℝ))).eval (-(a : ℝ) / b)| <
        1 / (|(D : ℝ)| * |(b : ℝ)| ^ q) := by
      apply lt_of_le_of_lt h
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (derivative_sum_le (by omega : j < q)) hε)
        (by positivity)).trans_lt hderiv
    rw [iterate_derivative_map] at h'
    have heval : ((derivative^[j] R).map (algebraMap ℚ ℝ)).eval (-(a : ℝ) / b) =
        (((derivative^[j] R).eval (-(a : ℚ) / b) : ℚ) : ℝ) := by
      rw [eval_map]
      simpa only [eq_ratCast, Rat.cast_div, Rat.cast_neg, Rat.cast_intCast] using
        (eval₂_at_apply (p := derivative^[j] R) (algebraMap ℚ ℝ) (-(a : ℚ) / b))
    rw [heval] at h'
    exact_mod_cast h'
  obtain ⟨M, hdiv⟩ := exact_linear_division (by exact_mod_cast hb) hzero
  refine ⟨M, quotient_degree (by exact_mod_cast hb) hRdeg hdiv,
    integral_scaled_quotient hab e hRlifts hdiv, ?_, ?_⟩
  · intro z hz0 hzN
    apply quotient_integral_at hab (hcop z hz0 hzN) e hRlifts _ hdiv
    have hx : (z : ℝ) ∈ Set.Icc 0 (N : ℝ) := ⟨by exact_mod_cast hz0, by exact_mod_cast hzN⟩
    obtain ⟨n, hn⟩ := hnear z hz0 hzN
    have hscaled := integral_eval_of_lifts hRlifts z
    simp only [eval_mul, eval_C] at hscaled
    have hRn : |(R.map (algebraMap ℚ ℝ)).eval (z : ℝ) - (n : ℝ)| < 1 / |(D : ℝ)| := by
      calc
        _ ≤ |(R.map (algebraMap ℚ ℝ)).eval (z : ℝ) - T.eval (z : ℝ)| + |T.eval (z : ℝ) - (n : ℝ)| := abs_sub_le _ _ _
        _ ≤ uniformConstant q * ε + ε := add_le_add (herr _ hx) hn
        _ = (uniformConstant q + 1) * ε := by ring
        _ < _ := hsmall
    have heval : (R.map (algebraMap ℚ ℝ)).eval (z : ℝ) = ((R.eval (z : ℚ) : ℚ) : ℝ) := by
      rw [eval_map]
      simpa only [eq_ratCast, Rat.cast_intCast] using (eval₂_at_apply (p := R) (algebraMap ℚ ℝ) (z : ℚ))
    rw [heval] at hRn
    have heq := integral_eq_of_near hD hscaled n (by exact_mod_cast hRn)
    exact ⟨n, heq.symm⟩
  · intro x hx
    have h := herr x hx
    rw [hdiv] at h
    simp [T] at h
    simp only [eval_map_algebraMap]
    convert h using 1
    ring_nf

end ExactInterpolation

 

 

end
end
end

end OAI

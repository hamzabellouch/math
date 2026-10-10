import Mathlib

namespace OAI

/-!
# Meixner and Pollaczek generating coefficients

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Filter Topology
open scoped BigOperators
variable {𝕜 : Type*} [RCLike 𝕜]
noncomputable def taylorCoeff (f : 𝕜 → 𝕜) (n : ℕ) : 𝕜 :=
  iteratedDeriv n f 0/(n.factorial:𝕜)
lemma taylorCoeff_zero (f : 𝕜 → 𝕜) : taylorCoeff f 0=f 0 := by simp [taylorCoeff]
lemma taylorCoeff_one (f : 𝕜 → 𝕜) : taylorCoeff f 1=deriv f 0 := by simp [taylorCoeff]
lemma taylorCoeff_congr {f g : 𝕜 → 𝕜} (h : f =ᶠ[𝓝 0] g) (n : ℕ) :
    taylorCoeff f n=taylorCoeff g n := by rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq n]
lemma taylorCoeff_add {f g : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (hg : ContDiffAt 𝕜 ⊤ g 0) (n : ℕ) :
    taylorCoeff (fun t => f t+g t) n=taylorCoeff f n+taylorCoeff g n := by
  rw [taylorCoeff,iteratedDeriv_fun_add (hf.of_le (by simp)) (hg.of_le (by simp)),add_div];rfl
lemma taylorCoeff_sub {f g : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (hg : ContDiffAt 𝕜 ⊤ g 0) (n : ℕ) :
    taylorCoeff (fun t => f t-g t) n=taylorCoeff f n-taylorCoeff g n := by
  change iteratedDeriv n (f-g) 0/(n.factorial:𝕜)=_
  rw [iteratedDeriv_sub (hf.of_le (by simp)) (hg.of_le (by simp)),sub_div];rfl
lemma taylorCoeff_const_mul (c : 𝕜) (f : 𝕜 → 𝕜) (n : ℕ) :
    taylorCoeff (fun t => c*f t) n=c*taylorCoeff f n := by
  rw [taylorCoeff,iteratedDeriv_const_mul_field]
  unfold taylorCoeff
  ring
lemma taylorCoeff_deriv (f : 𝕜 → 𝕜) (n : ℕ) :
    taylorCoeff (deriv f) n=(n+1)*taylorCoeff f (n+1) := by
  unfold taylorCoeff
  rw [←iteratedDeriv_succ',Nat.factorial_succ]
  push_cast
  field_simp
lemma taylorCoeff_monomial_mul {f : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (n k : ℕ) :
    taylorCoeff (fun t => t^k*f t) (n+k)=taylorCoeff f n := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_mul (by fun_prop) (hf.of_le (by simp))]
  simp_rw [iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true,Nat.add_sub_cancel]
    have he : ((n+k).choose k:𝕜)*(k.factorial:𝕜)*(n.factorial:𝕜)=((n+k).factorial:𝕜) := by
      exact_mod_cast (by simpa [mul_assoc,mul_left_comm,mul_comm] using Nat.add_choose_mul_factorial_mul_factorial n k : (n+k).choose k*k.factorial*n.factorial=(n+k).factorial)
    have hn : (n.factorial:𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hnk : ((n+k).factorial:𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+k)
    field_simp
    rw [←he]
    ring
  · intro j hj hjk;simp [hjk]
  · simp
lemma taylorCoeff_monomial_mul_low {f : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) {n k : ℕ} (h : n < k) :
    taylorCoeff (fun t => t^k*f t) n=0 := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_mul (by fun_prop) (hf.of_le (by simp))]
  apply div_eq_zero_iff.2
  left
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j ≤ n := by simpa using Finset.mem_range.1 hj
  rw [iteratedDeriv_fun_pow_zero,ite_eq_right (show j ≠ k by omega),Nat.cast_zero,mul_zero,zero_mul]
lemma taylorCoeff_id_mul {f : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (n : ℕ) :
    taylorCoeff (fun t => t*f t) (n+1)=taylorCoeff f n := by
  simpa using taylorCoeff_monomial_mul hf n 1
lemma taylorCoeff_sq_deriv {f : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (n : ℕ) :
    taylorCoeff (fun t => t^2*deriv f t) (n+1)=n*taylorCoeff f n := by
  have hd : ContDiffAt 𝕜 ⊤ (deriv f) 0 := hf.derivWithin (by simp)
  cases n with
  | zero => simp [taylorCoeff_monomial_mul_low hd (by norm_num : 1 < 2)]
  | succ n =>
    rw [show n+1+1=n+2 by omega,taylorCoeff_monomial_mul hd n 2,taylorCoeff_deriv]
    push_cast
    rfl
/-- Coefficient recurrence for the exact generating differential equation.
This is local at zero; no global power series assumption is made. -/
theorem taylorCoeff_ode_recurrence {f : 𝕜 → 𝕜} (hf : ContDiffAt 𝕜 ⊤ f 0) (a e : 𝕜)
    (hode : (fun t => (1-e*t^2)*deriv f t) =ᶠ[𝓝 0] (fun t => (a+e*t)*f t)) (n : ℕ) :
    (n+2)*taylorCoeff f (n+2)=a*taylorCoeff f (n+1)+e*(n+1)*taylorCoeff f n := by
  have hd : ContDiffAt 𝕜 ⊤ (deriv f) 0 := hf.derivWithin (by simp)
  have he : (fun t => deriv f t-e*(t^2*deriv f t)) =ᶠ[𝓝 0]
      (fun t => a*f t+e*(t*f t)) := by
    filter_upwards [hode] with t ht
    linear_combination ht
  have h := taylorCoeff_congr he (n+1)
  rw [taylorCoeff_sub hd (by fun_prop),taylorCoeff_add (by fun_prop) (by fun_prop),
    taylorCoeff_const_mul,taylorCoeff_const_mul,taylorCoeff_const_mul,
    taylorCoeff_deriv,taylorCoeff_sq_deriv hf,taylorCoeff_id_mul hf] at h
  push_cast at h ⊢
  linear_combination h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
/-! Coefficient bounds for `(1 + u)^(s - 1/2) (1 - u)^(-s - 1/2)`. Its even coefficients evaluate the polynomial Christoffel kernels at `-y²`, with `s = c*y/pi`. -/
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped BigOperators
noncomputable def meixnerCoeff (s : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2*s
  | n+2 => (2*s*meixnerCoeff s (n+1)+(n+1)*meixnerCoeff s n)/(n+2)
noncomputable def baseFactor (s : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+s+1/2)/(n+1)
noncomputable def factorError (s : ℝ) (n : ℕ) : ℝ := (2*s-1)^2/((2*n+2)*(2*n+3))
noncomputable def baseProduct (s : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n,baseFactor s j
noncomputable def upperProduct (s : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n,(baseFactor s j+factorError s j)
lemma baseFactor_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < baseFactor s n := by
  unfold baseFactor;positivity
lemma factorError_nonneg (s : ℝ) (n : ℕ) : 0 ≤ factorError s n := by
  unfold factorError;positivity
lemma baseProduct_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < baseProduct s n :=
  Finset.prod_pos (fun j _ => baseFactor_pos hs j)
lemma upperProduct_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < upperProduct s n :=
  Finset.prod_pos (fun j _ => add_pos_of_pos_of_nonneg (baseFactor_pos hs j) (factorError_nonneg s j))
lemma baseProduct_succ (s : ℝ) (n : ℕ) : baseProduct s (n+1)=baseProduct s n*baseFactor s n := by
  exact Finset.prod_range_succ _ _
lemma upperProduct_succ (s : ℝ) (n : ℕ) : upperProduct s (n+1)=upperProduct s n*(baseFactor s n+factorError s n) := by
  exact Finset.prod_range_succ _ _
lemma meixner_pair_step (s : ℝ) (n : ℕ) :
    meixnerCoeff s (2*(n+1))=((2*n+1)/(2*n+2):ℝ)*meixnerCoeff s (2*n)+
      (2*s/(2*n+2))*meixnerCoeff s (2*n+1) ∧
    meixnerCoeff s (2*(n+1)+1)=(2*s/(2*n+3))*meixnerCoeff s (2*(n+1))+
      ((2*n+2)/(2*n+3):ℝ)*meixnerCoeff s (2*n+1) := by
  constructor
  · rw [show 2*(n+1)=2*n+2 by omega,meixnerCoeff]
    push_cast
    ring
  · rw [show 2*(n+1)+1=(2*n+1)+2 by omega,meixnerCoeff]
    rw [show 2*n+1+1=2*(n+1) by omega]
    push_cast
    ring
lemma pair_rowsums (s : ℝ) (n : ℕ) :
    ((2*n+1)/(2*n+2):ℝ)+2*s/(2*n+2)=baseFactor s n ∧
    (2*s/(2*n+3))*baseFactor s n+(2*n+2)/(2*n+3)=baseFactor s n+factorError s n := by
  have h1 : (2*(n:ℝ)+2) ≠ 0 := by positivity
  have h2 : (2*(n:ℝ)+3) ≠ 0 := by positivity
  have h3 : (n:ℝ)+1 ≠ 0 := by positivity
  unfold baseFactor factorError
  constructor <;> field_simp <;> ring
lemma meixner_pair_lower {s : ℝ} (hs : 0 < s) (n : ℕ) :
    min 1 (2*s)*baseProduct s n ≤ meixnerCoeff s (2*n) ∧
    min 1 (2*s)*baseProduct s n ≤ meixnerCoeff s (2*n+1) := by
  have hm : 0 < min 1 (2*s) := lt_min (by norm_num) (by positivity)
  induction n with
  | zero => simp [baseProduct,meixnerCoeff]
  | succ n ih =>
    obtain ⟨he,ho⟩ := meixner_pair_step s n
    obtain ⟨hr,hr'⟩ := pair_rowsums s n
    have hA : 0 ≤ ((2*n+1)/(2*n+2):ℝ) := by positivity
    have hB : 0 ≤ 2*s/(2*n+2) := by positivity
    have hC : 0 ≤ 2*s/(2*n+3) := by positivity
    have hD : 0 ≤ ((2*n+2)/(2*n+3):ℝ) := by positivity
    have hE : 0 ≤ min 1 (2*s)*baseProduct s n := (mul_pos hm (baseProduct_pos hs n)).le
    have he' : min 1 (2*s)*baseProduct s (n+1) ≤ meixnerCoeff s (2*(n+1)) := by
      rw [baseProduct_succ,he]
      calc
        _=(((2*n+1)/(2*n+2):ℝ)+2*s/(2*n+2))*(min 1 (2*s)*baseProduct s n) := by rw [hr];ring
        _≤_ := by rw [add_mul];exact add_le_add (mul_le_mul_of_nonneg_left ih.1 hA) (mul_le_mul_of_nonneg_left ih.2 hB)
    refine ⟨he',?_⟩
    rw [ho,baseProduct_succ] at ⊢
    calc
      _≤(baseFactor s n+factorError s n)*(min 1 (2*s)*baseProduct s n) := by
        nlinarith [mul_nonneg (factorError_nonneg s n) hE]
      _=(2*s/(2*n+3))*(min 1 (2*s)*baseProduct s (n+1))+
          ((2*n+2)/(2*n+3):ℝ)*(min 1 (2*s)*baseProduct s n) := by rw [baseProduct_succ,←hr'];ring
      _≤_ := add_le_add (mul_le_mul_of_nonneg_left he' hC) (mul_le_mul_of_nonneg_left ih.2 hD)
lemma meixner_pair_upper {s : ℝ} (hs : 0 < s) (n : ℕ) :
    meixnerCoeff s (2*n) ≤ max 1 (2*s)*upperProduct s n ∧
    meixnerCoeff s (2*n+1) ≤ max 1 (2*s)*upperProduct s n := by
  have hm : 0 < max 1 (2*s) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  induction n with
  | zero => simp [upperProduct,meixnerCoeff]
  | succ n ih =>
    obtain ⟨he,ho⟩ := meixner_pair_step s n
    obtain ⟨hr,hr'⟩ := pair_rowsums s n
    have hA : 0 ≤ ((2*n+1)/(2*n+2):ℝ) := by positivity
    have hB : 0 ≤ 2*s/(2*n+2) := by positivity
    have hC : 0 ≤ 2*s/(2*n+3) := by positivity
    have hD : 0 ≤ ((2*n+2)/(2*n+3):ℝ) := by positivity
    have hE : 0 ≤ max 1 (2*s)*upperProduct s n := (mul_pos hm (upperProduct_pos hs n)).le
    have he' : meixnerCoeff s (2*(n+1)) ≤ (max 1 (2*s)*upperProduct s n)*baseFactor s n := by
      rw [he]
      calc
        _≤(((2*n+1)/(2*n+2):ℝ)+2*s/(2*n+2))*(max 1 (2*s)*upperProduct s n) := by
          rw [add_mul];exact add_le_add (mul_le_mul_of_nonneg_left ih.1 hA) (mul_le_mul_of_nonneg_left ih.2 hB)
        _=_ := by rw [hr];ring
    constructor
    · rw [upperProduct_succ]
      exact he'.trans (by nlinarith [mul_nonneg hE (factorError_nonneg s n)])
    · rw [ho,upperProduct_succ]
      calc
        _≤(2*s/(2*n+3))*((max 1 (2*s)*upperProduct s n)*baseFactor s n)+
              ((2*n+2)/(2*n+3):ℝ)*(max 1 (2*s)*upperProduct s n) :=
          add_le_add (mul_le_mul_of_nonneg_left he' hC) (mul_le_mul_of_nonneg_left ih.2 hD)
        _=_ := by rw [show (2*s/(2*n+3))*((max 1 (2*s)*upperProduct s n)*baseFactor s n)+
              ((2*n+2)/(2*n+3):ℝ)*(max 1 (2*s)*upperProduct s n)=
            (max 1 (2*s)*upperProduct s n)*((2*s/(2*n+3))*baseFactor s n+(2*n+2)/(2*n+3)) by ring,hr'];ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped BigOperators
lemma baseFactor_ge_half {s : ℝ} (hs : 0 < s) (n : ℕ) : (1:ℝ)/2 ≤ baseFactor s n := by
  unfold baseFactor
  apply (le_div_iff₀ (by positivity)).2
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]
lemma factorError_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    factorError s n ≤ baseFactor s n*((2*s-1)^2/((n:ℝ)+1)^2) := by
  have hden : 2*((n:ℝ)+1)^2 ≤ (2*n+2)*(2*n+3) := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]
  calc
    _≤(2*s-1)^2/(2*((n:ℝ)+1)^2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _=(1/2)*((2*s-1)^2/((n:ℝ)+1)^2) := by rw [div_mul_eq_div_div];ring
    _≤_ := mul_le_mul_of_nonneg_right (baseFactor_ge_half hs n) (by positivity)
lemma reciprocal_square_sum_bound (n : ℕ) :
    (∑ j ∈ Finset.range n,(1:ℝ)/((j:ℝ)+1)^2) ≤ 2-2/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hp : (0:ℝ) < n+1 := by positivity
    have hq : (0:ℝ) < n+2 := by positivity
    have hd : (1:ℝ)/((n:ℝ)+1)^2 ≤ 2/((n:ℝ)+1)-2/((n:ℝ)+2) := by
      apply (div_le_iff₀ (sq_pos_of_pos hp)).2
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have he : (n:ℝ)+1+1=(n:ℝ)+2 := by ring
    rw [he]
    linarith
lemma reciprocal_square_sum_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n,(1:ℝ)/((j:ℝ)+1)^2) ≤ 2 := by
  have h:=reciprocal_square_sum_bound n
  have hp : 0 ≤ (2:ℝ)/((n:ℝ)+1) := by positivity
  linarith
lemma upperProduct_le_exp {s : ℝ} (hs : 0 < s) (n : ℕ) :
    upperProduct s n ≤ baseProduct s n*Real.exp (2*(2*s-1)^2) := by
  have hf (j : ℕ) : baseFactor s j+factorError s j ≤
      baseFactor s j*Real.exp ((2*s-1)^2/((j:ℝ)+1)^2) := by
    calc
      _≤baseFactor s j*(1+(2*s-1)^2/((j:ℝ)+1)^2) := by nlinarith [factorError_le hs j]
      _≤_ := mul_le_mul_of_nonneg_left (by simpa [add_comm] using Real.add_one_le_exp ((2*s-1)^2/((j:ℝ)+1)^2)) (baseFactor_pos hs j).le
  calc
    _≤∏ j ∈ Finset.range n,baseFactor s j*Real.exp ((2*s-1)^2/((j:ℝ)+1)^2) := by
      apply Finset.prod_le_prod₀
      · intro j hj;exact add_nonneg (baseFactor_pos hs j).le (factorError_nonneg s j)
      · intro j hj;exact hf j
    _=baseProduct s n*Real.exp ((2*s-1)^2*(∑ j ∈ Finset.range n,(1:ℝ)/((j:ℝ)+1)^2)) := by
      rw [Finset.prod_mul_distrib,←Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _≤_ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two n) (sq_nonneg (2*s-1))])) (baseProduct_pos hs n).le
/-- Uniform bounds on the exact recurrence; the finite products have exponent
s-1/2, obtained by Euler's Gamma limit in ProductGammaAsymptotic. -/
theorem meixner_even_product_bounds {s : ℝ} (hs : 0 < s) (n : ℕ) :
    min 1 (2*s)*baseProduct s n ≤ meixnerCoeff s (2*n) ∧
    meixnerCoeff s (2*n) ≤ (max 1 (2*s)*Real.exp (2*(2*s-1)^2))*baseProduct s n := by
  refine ⟨(meixner_pair_lower hs n).1,?_⟩
  calc
    _ ≤ max 1 (2*s)*upperProduct s n := (meixner_pair_upper hs n).1
    _ ≤ max 1 (2*s)*(baseProduct s n*Real.exp (2*(2*s-1)^2)) :=
      mul_le_mul_of_nonneg_left (upperProduct_le_exp hs n) (by positivity)
    _=_ := by ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped BigOperators
noncomputable def pochRatio (a : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n,(a+j)/(j+1)
lemma pochRatio_formula (a : ℝ) (n : ℕ) :
    pochRatio a n=(∏ j ∈ Finset.range n,(a+j))/(n.factorial:ℝ) := by
  unfold pochRatio
  rw [Finset.prod_div_distrib]
  congr 1
  exact_mod_cast Finset.prod_range_add_one_eq_factorial n
lemma pochRatio_gamma_identity {a : ℝ} (ha : 0 < a) (n : ℕ) :
    GammaSeq a n*(pochRatio a (n+1)/((n:ℝ)+1)^(a-1))=((n:ℝ)/(n+1))^a := by
  have hp : (∏ j ∈ Finset.range (n+1),(a+j)) ≠ 0 :=
    (Finset.prod_pos (fun j _ => by positivity)).ne'
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hnf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hpow : ((n:ℝ)+1)^a ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [Real.div_rpow (Nat.cast_nonneg n) (by positivity),Real.rpow_sub_one hn,
    pochRatio_formula,GammaSeq,Nat.factorial_succ]
  push_cast
  field_simp
lemma pochRatio_normalized_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => pochRatio a (n+1)/((n:ℝ)+1)^(a-1)) atTop (𝓝 (1/Gamma a)) := by
  have hΓ : Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hq := ((tendsto_natCast_div_add_atTop (1:ℝ)).rpow_const (p:=a) (Or.inl one_ne_zero)).div
    (GammaSeq_tendsto_Gamma a) hΓ
  simp only [Real.one_rpow] at hq
  apply hq.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hgp : GammaSeq a n ≠ 0 := by
    unfold GammaSeq
    apply div_ne_zero
    · exact mul_ne_zero (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne' (by exact_mod_cast Nat.factorial_ne_zero n)
    · exact (Finset.prod_pos (fun j _ => by positivity)).ne'
  exact (eq_div_iff hgp).2 (by rw [mul_comm,pochRatio_gamma_identity ha]) |>.symm
/-- Constant-factor, not epsilon-loss, asymptotics for the rising-factorial
product needed by the polynomial determinant compression. -/
lemma pochRatio_eventual_bounds {a : ℝ} (ha : 0 < a) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c*((n:ℝ)+1)^(a-1) ≤ pochRatio a (n+1) ∧
      pochRatio a (n+1) ≤ C*((n:ℝ)+1)^(a-1) := by
  have hp : 0 < 1/Gamma a := one_div_pos.2 (Real.Gamma_pos_of_pos ha)
  have ht := pochRatio_normalized_tendsto ha
  refine ⟨(1/Gamma a)/2,2*(1/Gamma a),by positivity,by positivity,?_⟩
  have he := (tendsto_order.1 ht).1 ((1/Gamma a)/2) (by linarith)
  have hf := (tendsto_order.1 ht).2 (2*(1/Gamma a)) (by linarith)
  filter_upwards [he,hf] with n hn hm
  have hr : 0 < ((n:ℝ)+1)^(a-1) := Real.rpow_pos_of_pos (by positivity) _
  exact ⟨(le_div_iff₀ hr).1 hn.le,(div_le_iff₀ hr).1 hm.le⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped BigOperators
lemma positive_sequence_global_bounds {f : ℕ → ℝ} {l : ℝ}
    (hf : ∀ n,0 < f n) (hl : 0 < l) (ht : Tendsto f atTop (𝓝 l)) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n,c ≤ f n ∧ f n ≤ C := by
  obtain ⟨C,hC⟩ := ht.bddAbove_range
  obtain ⟨D,hD⟩ := (ht.inv₀ hl.ne').bddAbove_range
  have hc : 0 < C := lt_of_lt_of_le (hf 0) (hC (Set.mem_range_self 0))
  have hd : 0 < D := lt_of_lt_of_le (inv_pos.2 (hf 0)) (hD (Set.mem_range_self 0))
  refine ⟨D⁻¹,C,inv_pos.2 hd,hc,fun n => ⟨?_,hC (Set.mem_range_self n)⟩⟩
  exact (inv_le_comm₀ hd (hf n)).2 (hD (Set.mem_range_self n))
lemma baseProduct_eq_poch (s : ℝ) (n : ℕ) :
    baseProduct s n=pochRatio (s+1/2) n := by
  unfold baseProduct baseFactor pochRatio
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring
lemma pochRatio_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < pochRatio a n :=
  Finset.prod_pos (fun j _ => div_pos (by positivity) (by positivity))
lemma pochRatio_succ (a : ℝ) (n : ℕ) :
    pochRatio a (n+1)=pochRatio a n*((a+n)/(n+1)) := Finset.prod_range_succ _ _
lemma baseProduct_square_normalized_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => baseProduct s n^2/pochRatio (2*s) n) atTop
      (𝓝 ((1/Gamma (s+1/2))^2/(1/Gamma (2*s)))) := by
  have ha : 0 < s+1/2 := by linarith
  have hb : 0 < 2*s := by positivity
  have h := ((pochRatio_normalized_tendsto ha).pow 2).div
    (pochRatio_normalized_tendsto hb) (by positivity)
  have he (n : ℕ) : (pochRatio (s+1/2) (n+1)/((n:ℝ)+1)^(s+1/2-1))^2 /
      (pochRatio (2*s) (n+1)/((n:ℝ)+1)^(2*s-1))=
      baseProduct s (n+1)^2/pochRatio (2*s) (n+1) := by
    rw [baseProduct_eq_poch]
    have hp : (((n:ℝ)+1)^(s+1/2-1))^2=((n:ℝ)+1)^(2*s-1) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [div_pow,hp]
    field_simp
  apply (tendsto_add_atTop_iff_nat 1).1
  exact h.congr (fun n => he n)
lemma baseProduct_square_poch_bounds {s : ℝ} (hs : 0 < s) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n,
      c*pochRatio (2*s) n ≤ baseProduct s n^2 ∧
      baseProduct s n^2 ≤ C*pochRatio (2*s) n := by
  obtain ⟨c,C,hc,hC,h⟩ := positive_sequence_global_bounds
    (fun n => div_pos (sq_pos_of_pos (baseProduct_pos hs n)) (pochRatio_pos (by positivity) n))
    (by positivity : 0 < (1/Gamma (s+1/2))^2/(1/Gamma (2*s)))
    (baseProduct_square_normalized_tendsto hs)
  refine ⟨c,C,hc,hC,fun n => ?_⟩
  exact ⟨(le_div_iff₀ (pochRatio_pos (by positivity) n)).1 (h n).1,
    (div_le_iff₀ (pochRatio_pos (by positivity) n)).1 (h n).2⟩
lemma meixner_even_square_poch_bounds {s : ℝ} (hs : 0 < s) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n,
      c*pochRatio (2*s) n ≤ meixnerCoeff s (2*n)^2 ∧
      meixnerCoeff s (2*n)^2 ≤ C*pochRatio (2*s) n := by
  obtain ⟨c,C,hc,hC,h⟩ := baseProduct_square_poch_bounds hs
  let m := min 1 (2*s)
  let M := max 1 (2*s)*Real.exp (2*(2*s-1)^2)
  have hm : 0 < m := lt_min (by norm_num) (by positivity)
  have hM : 0 < M := by dsimp [M];positivity
  refine ⟨m^2*c,M^2*C,by positivity,by positivity,fun n => ?_⟩
  have hb := meixner_even_product_bounds hs n
  change m*baseProduct s n ≤ _ ∧ _ ≤ M*baseProduct s n at hb
  have hbp : 0 < baseProduct s n := baseProduct_pos hs n
  have hp : 0 ≤ meixnerCoeff s (2*n) := le_trans (by positivity) hb.1
  constructor
  · have hl := mul_self_le_mul_self (by positivity : 0 ≤ m*baseProduct s n) hb.1
    have hl' := mul_le_mul_of_nonneg_left (h n).1 (sq_nonneg m)
    nlinarith
  · have hu := mul_self_le_mul_self hp hb.2
    have hu' := mul_le_mul_of_nonneg_left (h n).2 (sq_nonneg M)
    nlinarith
lemma sum_pochRatio {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1),pochRatio a j)=((n:ℝ)+1)/a*pochRatio a (n+1) := by
  induction n with
  | zero => simp [pochRatio];field_simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,pochRatio_succ a (n+1)]
    push_cast
    field_simp
    ring
noncomputable def evenCoefficientKernel (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),meixnerCoeff s (2*j)^2
/-- The exact squared-coefficient sum needed for the negative-axis
Christoffel kernel. The link with the orthogonal polynomial generating
function is a separate obligation, not an assumed kernel identification. -/
theorem evenCoefficientKernel_bounds {s : ℝ} (hs : 0 < s) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c*((n:ℝ)+1)^(2*s) ≤ evenCoefficientKernel s n ∧
      evenCoefficientKernel s n ≤ C*((n:ℝ)+1)^(2*s) := by
  obtain ⟨c,C,hc,hC,h⟩ := meixner_even_square_poch_bounds hs
  obtain ⟨d,D,hd,hD,hp⟩ := pochRatio_eventual_bounds (show 0 < 2*s by positivity)
  refine ⟨c*d/(2*s),C*D/(2*s),by positivity,by positivity,?_⟩
  filter_upwards [hp] with n hn
  have hlo : c*(((n:ℝ)+1)/(2*s)*pochRatio (2*s) (n+1)) ≤ evenCoefficientKernel s n := by
    rw [←sum_pochRatio (by positivity),Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (h j).1)
  have hhi : evenCoefficientKernel s n ≤ C*(((n:ℝ)+1)/(2*s)*pochRatio (2*s) (n+1)) := by
    rw [←sum_pochRatio (by positivity),Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (h j).2)
  have he : ((n:ℝ)+1)*((n:ℝ)+1)^(2*s-1)=((n:ℝ)+1)^(2*s) := by
    rw [Real.rpow_sub_one (by positivity)]
    field_simp
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hn.1 (show 0 ≤ c*(((n:ℝ)+1)/(2*s)) by positivity)
    calc
      _=c*(((n:ℝ)+1)/(2*s)*(d*((n:ℝ)+1)^(2*s-1))) := by rw [←he];ring
      _≤c*(((n:ℝ)+1)/(2*s)*pochRatio (2*s) (n+1)) := by simpa [mul_assoc] using hmul
      _≤_ := hlo
  · have hmul := mul_le_mul_of_nonneg_left hn.2 (show 0 ≤ C*(((n:ℝ)+1)/(2*s)) by positivity)
    calc
      _≤C*(((n:ℝ)+1)/(2*s)*pochRatio (2*s) (n+1)) := hhi
      _≤C*(((n:ℝ)+1)/(2*s)*(D*((n:ℝ)+1)^(2*s-1))) := by simpa [mul_assoc] using hmul
      _=_ := by rw [←he];ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
noncomputable def meixnerGenerator (s u : ℝ) : ℝ :=
  (1+u)^(s-1/2)*(1-u)^(-s-1/2)
lemma meixnerGenerator_smooth (s : ℝ) : ContDiffAt ℝ ⊤ (meixnerGenerator s) 0 := by
  apply ContDiffAt.mul
  · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by norm_num)
  · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by norm_num)
lemma meixnerGenerator_zero (s : ℝ) : meixnerGenerator s 0=1 := by simp [meixnerGenerator]
lemma meixnerGenerator_ode (s : ℝ) :
    (fun u => (1-u^2)*deriv (meixnerGenerator s) u) =ᶠ[𝓝 0]
      (fun u => (2*s+u)*meixnerGenerator s u) := by
  have hi : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 0 := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hi] with u hu
  have hp : 0 < 1+u := by linarith [hu.1]
  have hm : 0 < 1-u := by linarith [hu.2]
  have h1 := (Real.hasDerivAt_rpow_const (x:=1+u) (p:=s-1/2) (Or.inl hp.ne')).comp u
    ((hasDerivAt_id u).const_add 1)
  have h2 := (Real.hasDerivAt_rpow_const (x:=1-u) (p:=-s-1/2) (Or.inl hm.ne')).comp u
    ((hasDerivAt_id u).const_sub 1)
  have hder := (h1.mul h2).deriv
  change deriv (meixnerGenerator s) u=_ at hder
  rw [hder,Real.rpow_sub_one hp.ne',Real.rpow_sub_one hm.ne']
  unfold meixnerGenerator
  dsimp only [Function.comp_apply]
  field_simp
  ring
lemma meixnerGenerator_one_coeff (s : ℝ) : taylorCoeff (meixnerGenerator s) 1=2*s := by
  have h:= (meixnerGenerator_ode s).eq_of_nhds
  simpa [taylorCoeff_one,meixnerGenerator_zero] using h
/-- The recurrence coefficients equal the Taylor coefficients of the generating function. -/
lemma meixnerGenerator_taylor (s : ℝ) (n : ℕ) :
    taylorCoeff (meixnerGenerator s) n=meixnerCoeff s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [taylorCoeff_zero,meixnerGenerator_zero,meixnerCoeff]
  | one => simp [meixnerGenerator_one_coeff,meixnerCoeff]
  | more n ih0 ih1 =>
    have he := taylorCoeff_ode_recurrence (meixnerGenerator_smooth s) (2*s) 1
      (by simpa using meixnerGenerator_ode s) n
    rw [ih0,ih1] at he
    rw [meixnerCoeff]
    apply (eq_div_iff (by positivity : (n:ℝ)+2 ≠ 0)).2
    convert he using 1 <;> ring
noncomputable def meixnerEvenGenerator (s u : ℝ) : ℝ :=
  (1-u^2)^(-(1:ℝ)/2)*Real.cosh (2*s*Real.artanh u)
lemma meixnerGenerator_exp {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) (s : ℝ) :
    meixnerGenerator s u=(1-u^2)^(-(1:ℝ)/2)*Real.exp (2*s*Real.artanh u) := by
  have hp : 0 < 1+u := by linarith [hu.1]
  have hm : 0 < 1-u := by linarith [hu.2]
  have hsq : 0 < 1-u^2 := by nlinarith [mul_pos hp hm]
  rw [meixnerGenerator,Real.rpow_def_of_pos hp,Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos hsq,Real.artanh_eq_half_log ⟨hu.1.le,hu.2.le⟩,
    Real.log_div hp.ne' hm.ne',←Real.exp_add,←Real.exp_add]
  have hlog : Real.log (1-u^2)=Real.log (1+u)+Real.log (1-u) := by
    rw [show 1-u^2=(1+u)*(1-u) by ring,Real.log_mul hp.ne' hm.ne']
  rw [hlog]
  congr 1
  ring
lemma meixnerEvenGenerator_eq {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) (s : ℝ) :
    meixnerEvenGenerator s u=(meixnerGenerator s u+meixnerGenerator s (-u))/2 := by
  rw [meixnerGenerator_exp hu,meixnerGenerator_exp (u:=-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩]
  have hp : 0 < 1+u := by linarith [hu.1]
  have hm : 0 < 1-u := by linarith [hu.2]
  have ha : Real.artanh (-u) = -Real.artanh u := by
    rw [Real.artanh_eq_half_log ⟨by linarith [hu.2],by linarith [hu.1]⟩,
      Real.artanh_eq_half_log ⟨hu.1.le,hu.2.le⟩]
    simp only [←sub_eq_add_neg,sub_neg_eq_add]
    rw [Real.log_div hm.ne' hp.ne',Real.log_div hp.ne' hm.ne']
    ring
  simp only [neg_sq,ha]
  unfold meixnerEvenGenerator
  rw [Real.cosh_eq,show 2*s*(-Real.artanh u)=-(2*s*Real.artanh u) by ring]
  ring
lemma meixnerEvenGenerator_taylor (s : ℝ) (n : ℕ) :
    taylorCoeff (meixnerEvenGenerator s) (2*n)=meixnerCoeff s (2*n) := by
  have he : meixnerEvenGenerator s =ᶠ[𝓝 0]
      (fun u => (meixnerGenerator s u+meixnerGenerator s (-u))/2) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with u hu
    exact meixnerEvenGenerator_eq hu s
  rw [taylorCoeff_congr he]
  unfold taylorCoeff
  have hneg : ContDiffAt ℝ ⊤ (fun u => meixnerGenerator s (-u)) 0 := by
    have hf : ContDiffAt ℝ ⊤ (meixnerGenerator s) (-(0:ℝ)) := by simpa using meixnerGenerator_smooth s
    exact hf.comp (0:ℝ) (show ContDiffAt ℝ ⊤ (fun u : ℝ => -u) 0 by fun_prop)
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_add (meixnerGenerator_smooth s |>.of_le (by simp))
    (hneg.of_le (by simp)),iteratedDeriv_comp_neg]
  simp only [neg_zero,pow_mul,neg_one_sq,one_pow,one_smul]
  rw [←meixnerGenerator_taylor s (2*n)]
  unfold taylorCoeff
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial
noncomputable def evenOddPolynomials (e : ℝ) : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1,C 2)
  | n+1 =>
    let E := (evenOddPolynomials e n).1
    let O := (evenOddPolynomials e n).2
    let E' := C ((2*(n:ℝ)+2)⁻¹)*(C 2*X*O+C (e*(2*n+1))*E)
    (E',C ((2*(n:ℝ)+3)⁻¹)*(C 2*E'+C (e*(2*n+2))*O))
noncomputable def evenPoly (e : ℝ) (n : ℕ) : Polynomial ℝ := (evenOddPolynomials e n).1
noncomputable def oddPoly (e : ℝ) (n : ℕ) : Polynomial ℝ := (evenOddPolynomials e n).2
@[simp] lemma evenPoly_zero (e : ℝ) : evenPoly e 0=1 := rfl
@[simp] lemma oddPoly_zero (e : ℝ) : oddPoly e 0=C 2 := rfl
lemma evenPoly_succ (e : ℝ) (n : ℕ) : evenPoly e (n+1)=
    C ((2*(n:ℝ)+2)⁻¹)*(C 2*X*oddPoly e n+C (e*(2*n+1))*evenPoly e n) := rfl
lemma oddPoly_succ (e : ℝ) (n : ℕ) : oddPoly e (n+1)=
    C ((2*(n:ℝ)+3)⁻¹)*(C 2*evenPoly e (n+1)+C (e*(2*n+2))*oddPoly e n) := rfl
lemma eval_evenPoly_succ (e x : ℝ) (n : ℕ) :
    (evenPoly e (n+1)).eval x=(2*x*(oddPoly e n).eval x+e*(2*n+1)*(evenPoly e n).eval x)/(2*n+2) := by
  rw [evenPoly_succ];simp;ring
lemma eval_oddPoly_succ (e x : ℝ) (n : ℕ) :
    (oddPoly e (n+1)).eval x=(2*(evenPoly e (n+1)).eval x+e*(2*n+2)*(oddPoly e n).eval x)/(2*n+3) := by
  rw [oddPoly_succ];simp;ring
lemma meixnerCoeff_even_step (s : ℝ) (n : ℕ) :
    meixnerCoeff s (2*(n+1))=(2*s*meixnerCoeff s (2*n+1)+(2*n+1)*meixnerCoeff s (2*n))/(2*n+2) := by
  rw [show 2*(n+1)=2*n+2 by omega,meixnerCoeff];push_cast;ring
lemma meixnerCoeff_odd_step (s : ℝ) (n : ℕ) :
    meixnerCoeff s (2*(n+1)+1)=(2*s*meixnerCoeff s (2*(n+1))+(2*n+2)*meixnerCoeff s (2*n+1))/(2*n+3) := by
  rw [show 2*(n+1)+1=(2*n+1)+2 by omega,meixnerCoeff]
  simp only [show 2*n+1+1=2*(n+1) by omega];push_cast;ring
/-- The even Pollaczek polynomials form a basis. -/
lemma evenOdd_plus_eval (s : ℝ) (n : ℕ) :
    (evenPoly 1 n).eval (s^2)=meixnerCoeff s (2*n) ∧
    s*(oddPoly 1 n).eval (s^2)=meixnerCoeff s (2*n+1) := by
  induction n with
  | zero => simp [meixnerCoeff,mul_comm]
  | succ n ih =>
    have he : (evenPoly 1 (n+1)).eval (s^2)=meixnerCoeff s (2*(n+1)) := by
      rw [eval_evenPoly_succ,meixnerCoeff_even_step,←ih.1,←ih.2];ring
    refine ⟨he,?_⟩
    rw [eval_oddPoly_succ,meixnerCoeff_odd_step,he,←ih.2];ring
lemma evenOdd_sign_eval (x : ℝ) (n : ℕ) :
    (evenPoly (-1) n).eval (-x)=(-1)^n*(evenPoly 1 n).eval x ∧
    (oddPoly (-1) n).eval (-x)=(-1)^n*(oddPoly 1 n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (evenPoly (-1) (n+1)).eval (-x)=(-1)^(n+1)*(evenPoly 1 (n+1)).eval x := by
      rw [eval_evenPoly_succ,eval_evenPoly_succ,ih.1,ih.2,pow_succ];ring
    refine ⟨he,?_⟩
    rw [eval_oddPoly_succ,eval_oddPoly_succ,he,ih.2,pow_succ];ring
/-- Evaluation on the negative axis gives alternating Meixner coefficients. -/
lemma evenPoly_negative_eval (s : ℝ) (n : ℕ) :
    (evenPoly (-1) n).eval (-(s^2))=(-1)^n*meixnerCoeff s (2*n) := by
  rw [(evenOdd_sign_eval (s^2) n).1,(evenOdd_plus_eval s n).1]
lemma evenPoly_negative_eval_sq (s : ℝ) (n : ℕ) :
    ((evenPoly (-1) n).eval (-(s^2)))^2=(meixnerCoeff s (2*n))^2 := by
  rw [evenPoly_negative_eval,mul_pow,←pow_mul, mul_comm n 2,pow_mul,neg_one_sq,one_pow,one_mul]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped ContDiff
noncomputable def pollaczekGenerator (p t : ℝ) : ℝ :=
  (1+t^2)^(-(1:ℝ)/2)*Real.exp (2*p*Real.arctan t)
lemma pollaczekGenerator_smooth (p : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (pollaczekGenerator p) := by
  apply contDiff_iff_contDiffAt.2
  intro t
  apply ContDiffAt.mul
  · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by positivity)
  · exact (contDiffAt_const.mul (Real.contDiff_arctan (n:=n)).contDiffAt).exp
lemma pollaczekGenerator_analytic (p t : ℝ) : AnalyticAt ℝ (pollaczekGenerator p) t :=
  (pollaczekGenerator_smooth p (n:=ω)).contDiffAt.analyticAt
@[simp] lemma pollaczekGenerator_zero (p : ℝ) : pollaczekGenerator p 0=1 := by simp [pollaczekGenerator]
lemma pollaczekGenerator_ode (p t : ℝ) :
    (1+t^2)*deriv (pollaczekGenerator p) t=(2*p-t)*pollaczekGenerator p t := by
  have hp : 0 < 1+t^2 := by positivity
  have h1 := (Real.hasDerivAt_rpow_const (x:=1+t^2) (p:=-(1:ℝ)/2) (Or.inl hp.ne')).comp t
    (((hasDerivAt_id t).pow 2).const_add 1)
  have h2 := ((Real.hasDerivAt_arctan t).const_mul (2*p)).exp
  have hd := (h1.mul h2).deriv
  change deriv (pollaczekGenerator p) t=_ at hd
  rw [hd,Real.rpow_sub_one hp.ne']
  unfold pollaczekGenerator
  simp only [Function.comp_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring
noncomputable def pollaczekCoeff (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2*p
  | n+2 => (2*p*pollaczekCoeff p (n+1)-(n+1)*pollaczekCoeff p n)/(n+2)
lemma pollaczekGenerator_taylor (p : ℝ) (n : ℕ) :
    taylorCoeff (pollaczekGenerator p) n=pollaczekCoeff p n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [taylorCoeff_zero,pollaczekCoeff]
  | one =>
    have h := pollaczekGenerator_ode p 0
    simpa [taylorCoeff_one,pollaczekCoeff] using h
  | more n ih0 ih1 =>
    have hode : (fun t => (1-(-1)*t^2)*deriv (pollaczekGenerator p) t) =ᶠ[𝓝 0]
        (fun t => (2*p+(-1)*t)*pollaczekGenerator p t) := by
      exact Eventually.of_forall (fun t => by simpa [sub_eq_add_neg] using pollaczekGenerator_ode p t)
    have he := taylorCoeff_ode_recurrence (pollaczekGenerator_smooth p |>.contDiffAt) (2*p) (-1) hode n
    rw [ih0,ih1] at he
    rw [pollaczekCoeff]
    apply (eq_div_iff (by positivity : (n:ℝ)+2 ≠ 0)).2
    convert he using 1 <;> ring
lemma pollaczekCoeff_even_step (p : ℝ) (n : ℕ) :
    pollaczekCoeff p (2*(n+1))=(2*p*pollaczekCoeff p (2*n+1)-(2*n+1)*pollaczekCoeff p (2*n))/(2*n+2) := by
  rw [show 2*(n+1)=2*n+2 by omega,pollaczekCoeff];push_cast;ring
lemma pollaczekCoeff_odd_step (p : ℝ) (n : ℕ) :
    pollaczekCoeff p (2*(n+1)+1)=(2*p*pollaczekCoeff p (2*(n+1))-(2*n+2)*pollaczekCoeff p (2*n+1))/(2*n+3) := by
  rw [show 2*(n+1)+1=(2*n+1)+2 by omega,pollaczekCoeff]
  simp only [show 2*n+1+1=2*(n+1) by omega];push_cast;ring
lemma pollaczekCoeff_evenOdd (p : ℝ) (n : ℕ) :
    (evenPoly (-1) n).eval (p^2)=pollaczekCoeff p (2*n) ∧
    p*(oddPoly (-1) n).eval (p^2)=pollaczekCoeff p (2*n+1) := by
  induction n with
  | zero => simp [pollaczekCoeff,mul_comm]
  | succ n ih =>
    have he : (evenPoly (-1) (n+1)).eval (p^2)=pollaczekCoeff p (2*(n+1)) := by
      rw [eval_evenPoly_succ,pollaczekCoeff_even_step,←ih.1,←ih.2];ring
    refine ⟨he,?_⟩
    rw [eval_oddPoly_succ,pollaczekCoeff_odd_step,he,←ih.2];ring
lemma meixnerCoeff_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ meixnerCoeff s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [meixnerCoeff]
  | one => simp [meixnerCoeff];positivity
  | more n ih0 ih1 => rw [meixnerCoeff];positivity
lemma pollaczekCoeff_abs_le (p : ℝ) (n : ℕ) :
    |pollaczekCoeff p n| ≤ meixnerCoeff |p| n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczekCoeff,meixnerCoeff]
  | one => simp [pollaczekCoeff,meixnerCoeff,abs_mul]
  | more n ih0 ih1 =>
    rw [pollaczekCoeff,meixnerCoeff,abs_div,abs_of_pos (by positivity : 0 < (n:ℝ)+2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ |2*p*pollaczekCoeff p (n+1)|+|((n:ℝ)+1)*pollaczekCoeff p n| := abs_sub _ _
      _ = 2*|p| *|pollaczekCoeff p (n+1)|+((n:ℝ)+1)*|pollaczekCoeff p n| := by
        simp [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n+1 by positivity)]
      _ ≤ _ := by gcongr
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped BigOperators
lemma scalarSeries_taylor {f : ℝ → ℝ} {a : ℕ → ℝ}
    (h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ a) 0) (n : ℕ) :
    taylorCoeff f n=a n := by
  obtain ⟨r,hr⟩ := h
  have he := hr.factorial_smul (1:ℝ) n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq,nsmul_eq_mul,smul_eq_mul,
    one_pow,mul_one] at he
  rw [←iteratedDeriv_eq_iteratedFDeriv] at he
  exact (div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2 (by simpa [mul_comm] using he.symm)
noncomputable def binomialProductCoeff (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),Ring.choose a j*Ring.choose b (n-j)*(-1)^(n-j)
lemma binomialProduct_hasSum (a b : ℝ) {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n => binomialProductCoeff a b n*u^n) ((1+u)^a*(1-u)^b) := by
  have hu' : u ∈ Metric.eball (0:ℝ) 1 := by
    rw [mem_eball_zero_iff,enorm_eq_nnnorm]
    exact_mod_cast (show ‖u‖ < 1 by simpa [Real.norm_eq_abs] using hu)
  have hmu' : -u ∈ Metric.eball (0:ℝ) 1 := by simpa only [enorm_neg,mem_eball_zero_iff] using hu'
  have ha := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a:=a)).hasSum hu'
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a:=b)).hasSum hmu'
  simp only [zero_add,binomialSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] at ha hb
  have h := hasSum_sum_range_mul_of_summable_norm ha.summable.norm hb.summable.norm
  rw [ha.tsum_eq,hb.tsum_eq] at h
  convert! h using 1
  · funext n
    unfold binomialProductCoeff
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by simpa using Finset.mem_range.1 hj
    rw [neg_pow]
    have he : u^n=u^j*u^(n-j) := by rw [←pow_add,Nat.add_sub_of_le hj']
    rw [he]
    ring
lemma binomialProduct_series (a b : ℝ) :
    HasFPowerSeriesAt (fun u => (1+u)^a*(1-u)^b)
      (FormalMultilinearSeries.ofScalars ℝ (binomialProductCoeff a b)) 0 := by
  apply hasFPowerSeriesAt_iff.2
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with u hu
  have hu' : |u| < 1 := by simpa [Metric.mem_ball] using hu
  simpa [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,mul_comm] using binomialProduct_hasSum a b hu'
lemma meixnerCoeff_eq_binomialProduct (s : ℝ) (n : ℕ) :
    meixnerCoeff s n=binomialProductCoeff (s-1/2) (-s-1/2) n := by
  rw [←meixnerGenerator_taylor]
  exact scalarSeries_taylor (binomialProduct_series _ _) n
/-- The generating series converges absolutely for arguments of absolute value less than one. -/
lemma meixnerCoeff_hasSum (s : ℝ) {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n => meixnerCoeff s n*u^n) (meixnerGenerator s u) := by
  simpa only [meixnerCoeff_eq_binomialProduct,meixnerGenerator] using binomialProduct_hasSum (s-1/2) (-s-1/2) hu
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
open scoped NNReal ENNReal
lemma pollaczekCoeff_summable_norm (p : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => |pollaczekCoeff p n| *r^n) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (pollaczekCoeff_abs_le p n) (pow_nonneg hr0 n))
    (meixnerCoeff_hasSum |p| (by rwa [abs_of_nonneg hr0])).summable
lemma pollaczekCoeff_radius (p : ℝ) :
    (1:ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℝ (pollaczekCoeff p)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  apply FormalMultilinearSeries.le_radius_of_summable
  simpa only [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using
    pollaczekCoeff_summable_norm p r.coe_nonneg (by exact_mod_cast hr)
lemma pollaczekCoeff_hasSum (p : ℝ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => pollaczekCoeff p n*t^n) (pollaczekGenerator p t) := by
  have hc : (fun n => iteratedDeriv n (pollaczekGenerator p) 0 / n.factorial)=pollaczekCoeff p :=
    funext (pollaczekGenerator_taylor p)
  have ha : AnalyticOn ℝ (pollaczekGenerator p) (Metric.eball 0 1) :=
    fun t _ => (pollaczekGenerator_analytic p t).analyticWithinAt
  have hs := ha.hasFPowerSeriesOnSubball (by norm_num : (0:ENNReal)<1)
  simp only [hc] at hs
  have hmem : t ∈ Metric.eball (0:ℝ) 1 := by
    rw [mem_eball_zero_iff,enorm_eq_nnnorm]
    exact_mod_cast (show ‖t‖ < 1 by simpa [Real.norm_eq_abs] using ht)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,zero_add] using
    (hs (pollaczekCoeff_radius p)).hasSum hmem
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology MeasureTheory
noncomputable def pollaczekMajorant (p : ℝ) : ℝ := meixnerGenerator |p| (1/4)
lemma quarter_artanh_bounds : 0 ≤ Real.artanh (1/4) ∧ 4*Real.artanh (1/4) < Real.pi := by
  have he : Real.artanh (1/4)=Real.log (5/3)/2 := by
    rw [Real.artanh_eq_half_log (by norm_num : (1/4:ℝ) ∈ Set.Icc (-1) 1)];norm_num;ring
  rw [he]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5/3)
  have h0 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 5/3)
  constructor <;> linarith [Real.pi_gt_three]
lemma pollaczekMajorant_pos (p : ℝ) : 0 < pollaczekMajorant p := by
  unfold pollaczekMajorant meixnerGenerator
  positivity
lemma pollaczekMajorant_continuous : Continuous pollaczekMajorant := by
  unfold pollaczekMajorant meixnerGenerator
  fun_prop (disch := norm_num)
lemma pollaczekMajorant_exp {p : ℝ} (hp : 0 ≤ p) :
    pollaczekMajorant p=(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)*Real.exp (2*Real.artanh (1/4)*p) := by
  rw [pollaczekMajorant,abs_of_nonneg hp,meixnerGenerator_exp (by norm_num)]
  congr 2; ring
lemma exp_div_cosh_integrable {a : ℝ} (ha : a < Real.pi) :
    IntegrableOn (fun p => Real.exp (a*p)/Real.cosh (Real.pi*p)) (Set.Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (a:=a-Real.pi) (by linarith) 0).const_mul 2
  have hc : Continuous (fun p : ℝ => Real.exp (a*p)/Real.cosh (Real.pi*p)) :=
    (show Continuous (fun p : ℝ => Real.exp (a*p)) by fun_prop).div
      (by fun_prop) (fun p => (Real.cosh_pos _).ne')
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hc : Real.exp (Real.pi*p)/2 ≤ Real.cosh (Real.pi*p) := by
    rw [Real.cosh_eq];linarith [Real.exp_pos (-(Real.pi*p))]
  calc
    _ ≤ Real.exp (a*p)/(Real.exp (Real.pi*p)/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hc
    _ = 2*Real.exp ((a-Real.pi)*p) := by
      rw [sub_mul,Real.exp_sub];ring
lemma pollaczekMajorant_sq_integrable :
    IntegrableOn (fun p => pollaczekMajorant p^2/Real.cosh (Real.pi*p)) (Set.Ioi 0) := by
  have hi := (exp_div_cosh_integrable quarter_artanh_bounds.2).const_mul
    (((1-(1/4:ℝ)^2)^(-(1:ℝ)/2))^2)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [pollaczekMajorant_exp hp.le]
  rw [show 4*Real.artanh (1/4)*p=2*Real.artanh (1/4)*p+2*Real.artanh (1/4)*p by ring]
  rw [Real.exp_add]
  ring
lemma pollaczekCoeff_majorant (p : ℝ) (n : ℕ) :
    |pollaczekCoeff p n| ≤ 4^n*pollaczekMajorant p := by
  have hs := meixnerCoeff_hasSum |p| (u:=1/4) (by norm_num)
  have hn := hs.summable.le_tsum n (fun j _ => mul_nonneg (meixnerCoeff_nonneg (abs_nonneg p) j) (by positivity))
  rw [hs.tsum_eq] at hn
  have h := (mul_le_mul_of_nonneg_right (pollaczekCoeff_abs_le p n) (show (0:ℝ) ≤ (1/4)^n by positivity)).trans hn
  have he : (4:ℝ)^n*(1/4)^n=1 := by rw [←mul_pow];norm_num
  calc
    _ = 4^n*(|pollaczekCoeff p n| *(1/4)^n) := by linear_combination -|pollaczekCoeff p n| * he
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
lemma pollaczekGenerator_majorant (p : ℝ) {t : ℝ} (ht : |t| ≤ 1/4) :
    |pollaczekGenerator p t| ≤ pollaczekMajorant p := by
  have hs := pollaczekCoeff_hasSum p (t:=t) (by linarith)
  have hm := meixnerCoeff_hasSum |p| (u:=1/4) (by norm_num)
  rw [←Real.norm_eq_abs,←hs.tsum_eq]
  apply (norm_tsum_le_tsum_norm hs.summable.norm).trans
  unfold pollaczekMajorant
  rw [←hm.tsum_eq]
  apply hs.summable.norm.tsum_le_tsum _ hm.summable
  intro n
  simp only [norm_mul,Real.norm_eq_abs,abs_pow]
  exact mul_le_mul (pollaczekCoeff_abs_le p n) (pow_le_pow_left₀ (abs_nonneg t) ht n)
    (by positivity) (meixnerCoeff_nonneg (abs_nonneg p) n)
lemma pollaczekCoeff_continuous (n : ℕ) : Continuous (fun p => pollaczekCoeff p n) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [pollaczekCoeff] using continuous_const (y:=(1:ℝ))
  | one => simp only [pollaczekCoeff];fun_prop
  | more n ih0 ih1 => simp only [pollaczekCoeff];fun_prop
lemma pollaczekGenerator_continuous_p (t : ℝ) : Continuous (fun p => pollaczekGenerator p t) := by
  unfold pollaczekGenerator
  fun_prop
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI

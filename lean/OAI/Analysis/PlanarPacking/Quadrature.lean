import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.Analysis.PlanarPacking.Cardinal
import OAI.Analysis.PlanarPacking.Fejer

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma cheb_primitive_deriv (n : ℤ) (hn₁ : n+1 ≠ 0) (hn₂ : n-1 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (T ℝ (n+1)).eval x/(2*(n+1:ℤ))-
      (T ℝ (n-1)).eval x/(2*(n-1:ℤ))) ((T ℝ n).eval x) x := by
  have h := ((T ℝ (n+1)).hasDerivAt x).div_const (2*(n+1:ℤ) : ℝ)
  have h' := ((T ℝ (n-1)).hasDerivAt x).div_const (2*(n-1:ℤ) : ℝ)
  convert h.sub h' using 1 ; try rfl
  rw [T_derivative_eq_U, T_derivative_eq_U]
  simp only [eval_mul, eval_intCast]
  have hu := congrArg (fun p : ℝ[X] => p.eval x) (two_mul_T_eq_U_sub_U ℝ (n-2))
  simp only [sub_add_cancel, eval_mul, eval_sub, eval_ofNat] at hu
  have hn₁' : (n+1:ℝ) ≠ 0 := by exact_mod_cast hn₁
  have hn₂' : (n-1:ℝ) ≠ 0 := by exact_mod_cast hn₂
  push_cast
  simp only [show n+1-1=n by omega, show n-1-1=n-2 by omega]
  field_simp
  nlinarith [hu]

lemma cheb_integral (n : ℕ) :
    (∫ x in (-1:ℝ)..1, (T ℝ n).eval x) =
    (1+(-1:ℝ)^n)/(1-(n:ℝ)^2) := by
  by_cases hn : n=1
  · subst n
    norm_num [integral_id]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => cheb_primitive_deriv (n:ℤ) (by omega) (by omega) x)
    ((T ℝ (n:ℤ)).continuous.intervalIntegrable (-1) 1)
  rw [h, T_eval_one, T_eval_one, T_eval_neg_one, T_eval_neg_one]
  have hp : ((n:ℤ)+1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_add]
  have hm : ((n:ℤ)-1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_sub]
  rw [hp, hm]
  simp only [Units.val_neg, Int.cast_neg]
  have hnat : (((n:ℤ).negOnePow : ℤ) : ℝ) = (-1:ℝ)^n := by
    rw [Int.cast_negOnePow]
    simp
  rw [hnat]
  push_cast
  have hn₁ : (n:ℝ)+1 ≠ 0 := by positivity
  have hn₂ : (n:ℝ)-1 ≠ 0 := by exact_mod_cast (by omega : (n:ℤ)-1 ≠ 0)
  have hn₃ : 1-(n:ℝ)^2 ≠ 0 := by
    intro hzero
    have : (n:ℝ)=1 := by have := Nat.cast_nonneg (α:=ℝ) n; nlinarith
    exact hn (by exact_mod_cast this)
  field_simp
  ring

lemma fejer_recip_telescope (a : ℕ) (ha : 1 ≤ a) :
    (2:ℝ)/(4*(a:ℝ)^2-1) = 1/(2*(a:ℝ)-1)-1/(2*(a:ℝ)+1) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have h₁ : 2*(a:ℝ)-1 ≠ 0 := by linarith
  have h₂ : 2*(a:ℝ)+1 ≠ 0 := by linarith
  have h₃ : 4*(a:ℝ)^2-1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma fejer_recip_sum (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih,
      fejer_recip_telescope (m+1) (by omega)]
    push_cast
    have he : 2*((m:ℝ)+1)-1=2*(m:ℝ)+1 := by ring
    rw [he]
    ring

lemma fejerWeight_pos (v : ℕ) : 1/(256*255:ℝ) ≤ fejerWeight v := by
  have hsum : (2:ℝ)*∑ a ∈ Finset.Icc (1:ℕ) 127,
      Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1) ≤ 254/255 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ a ∈ Finset.Icc (1:ℕ) 127, (2:ℝ)/(4*(a:ℝ)^2-1) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
        have hd : 0 < 4*(a:ℝ)^2-1 := by nlinarith
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.cos_le_one (2*(a:ℝ)*fejerAngle v)]) hd.le
      _ = 254/255 := by rw [fejer_recip_sum]; norm_num
  unfold fejerWeight
  linarith


noncomputable def fejerPolynomial :=
  1-∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1)) • T ℝ (2*a)

lemma fejerPolynomial_eval (v : ℕ) :
    fejerPolynomial.eval (fejerNode v) = 256*fejerWeight v := by
  unfold fejerPolynomial
  rw [eval_sub, eval_one, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul, fejerNode, T_real_cos]
  unfold fejerWeight
  simp only [Finset.mul_sum]
  push_cast
  rw [show ∀ x : ℝ, 256*(x/256)=x from fun x => by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma fejerPolynomial_degree : fejerPolynomial.degree ≤ 254 := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · norm_num
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro a ha
    apply (degree_smul_le _ _).trans
    rw [degree_T]
    have ha' := (Finset.mem_Icc.mp ha).2
    norm_cast
    omega

lemma fejer_weighted_orthogonal (n : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (∫ x, (T ℝ n).eval x ∂measureT) -
      ∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
        (∫ x, (T ℝ (2*a)).eval x*(T ℝ n).eval x ∂measureT) := by
  unfold fejerPolynomial
  simp only [eval_sub, eval_one, eval_finsetSum, eval_smul, smul_eq_mul,
    sub_mul, one_mul, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_sub (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)), MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro a ha
    exact integrable_measureT (by fun_prop)

lemma fejer_integral_zero :
    (∫ x, fejerPolynomial.eval x*(T ℝ 0).eval x ∂measureT) = Real.pi := by
  change (∫ x, fejerPolynomial.eval x*(T ℝ (0:ℕ)).eval x ∂measureT) = _
  rw [fejer_weighted_orthogonal 0]
  norm_num only [Nat.cast_zero] at *
  rw [integral_eval_T_real_measureT_zero]
  simp only [sub_eq_self]
  apply Finset.sum_eq_zero
  intro a ha
  have hne : 2*a ≠ (0:ℕ) := by have := (Finset.mem_Icc.mp ha).1; omega
  have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
  push_cast at h
  rw [h, mul_zero]

lemma fejer_integral_even (k : ℕ) (hk : k ∈ Finset.Icc 1 127) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k)).eval x ∂measureT) =
      Real.pi/(1-(2*(k:ℝ))^2) := by
  have hk₀ : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  have hcast : (2*(k:ℤ)) ≠ 0 := by omega
  have he := fejer_weighted_orthogonal (2*k)
  push_cast at he
  rw [he]
  rw [integral_eval_T_real_measureT_of_ne_zero hcast]
  rw [Finset.sum_eq_single_of_mem k hk]
  · have hh := integral_T_real_mul_self_measureT_of_ne_zero (by omega : 2*k ≠ 0)
    push_cast at hh
    rw [hh]
    rw [show 1-(2*(k:ℝ))^2 = -(4*(k:ℝ)^2-1) by ring]
    simp only [div_neg]
    ring
  · intro a ha hne
    have hne' : 2*a ≠ 2*k := by omega
    have hh := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne'
    push_cast at hh
    rw [hh, mul_zero]

lemma fejer_integral_odd (k : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k+1)).eval x ∂measureT) = 0 := by
  have hh := fejer_weighted_orthogonal (2*k+1)
  push_cast at hh
  rw [hh, integral_eval_T_real_measureT_of_ne_zero (by omega : (2*(k:ℤ)+1) ≠ 0)]
  have he : (∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
      (∫ x, (T ℝ (2*a)).eval x*(T ℝ (2*k+1)).eval x ∂measureT)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hne : 2*a ≠ 2*k+1 := by omega
    have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
    push_cast at h
    rw [h, mul_zero]
  rw [he, sub_self]

lemma fejer_cheb_integral (n : ℕ) (hn : n < 256) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, (T ℝ n).eval x) := by
  rw [cheb_integral]
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · have he : n=2*k := by omega
    rw [he] at hn ⊢
    by_cases hk₀ : k=0
    · subst k
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, add_self_div_two,
        zero_pow (by norm_num : 2 ≠ 0), sub_zero, div_one, one_add_one_eq_two,
        div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using fejer_integral_zero
    · rw [show ((2*k:ℕ):ℤ)=2*(k:ℤ) by push_cast; rfl,
        fejer_integral_even k (by simp only [Finset.mem_Icc]; omega)]
      simp only [pow_mul, neg_one_sq, one_pow, Nat.cast_mul, Nat.cast_ofNat]
      ring
  · subst n
    rw [show ((2*k+1:ℕ):ℤ)=2*(k:ℤ)+1 by push_cast; rfl, fejer_integral_odd]
    simp [pow_add, pow_mul]

lemma fejer_polynomial_integral (P : ℝ[X]) (hP : P.degree < 256) :
    (∫ x, fejerPolynomial.eval x * P.eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  have hmem : P ∈ degreeLT ℝ 256 := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio 256 = Finset.range 256 by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum, intervalIntegral.integral_finsetSum]
  · simp_rw [mul_left_comm (fejerPolynomial.eval _) (c _),
      MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (chebyshevTsequence ℝ n) = T ℝ n by rfl,
      fejer_cheb_integral n (Finset.mem_range.mp hn)]
    ring
  · intro n hn
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro n hn
    exact integrable_measureT (by fun_prop)

lemma fejer_exact (P : ℝ[X]) (hP : P.degree < 256) :
    ∑ v ∈ Finset.range 256, fejerWeight v * P.eval (fejerNode v) =
      (1/2:ℝ)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  by_cases hp : P=0
  · simp [hp]
  have hdP : P.natDegree ≤ 255 := by
    have : P.natDegree < (256:ℕ) := (natDegree_lt_iff_degree_lt hp).mpr hP
    omega
  have hdF : fejerPolynomial.natDegree ≤ 254 :=
    natDegree_le_iff_degree_le.mpr fejerPolynomial_degree
  have hd : (fejerPolynomial*P).degree < 2*256 := by
    apply lt_of_le_of_lt (degree_le_natDegree)
    have hnat : (fejerPolynomial*P).natDegree ≤ 509 :=
      (natDegree_mul_le).trans (by omega)
    exact_mod_cast (by omega : (fejerPolynomial*P).natDegree < 2*256)
  have h := integral_eq_sumZeroes (P:=fejerPolynomial*P) (by norm_num : 256 ≠ 0) hd
  simp only [eval_mul] at h
  rw [fejer_polynomial_integral P hP] at h
  unfold sumZeroes at h
  have he : ∀ v : ℕ, Real.cos (((2*(v:ℝ)+1)/512)*Real.pi) = fejerNode v := by
    intro v
    unfold fejerNode fejerAngle
    congr 1
    ring
  norm_num only [Nat.cast_ofNat] at h
  simp only [he, eval_mul, fejerPolynomial_eval] at h
  simp only [mul_assoc, ← Finset.mul_sum] at h
  have halg (A B : ℝ) (hab : Real.pi/2*A = Real.pi/256*(256*B)) :
      B=(1/2:ℝ)*A := by nlinarith only [hab, Real.pi_pos]
  exact halg _ _ h

lemma fejer_mass : ∑ v ∈ Finset.range 256, fejerWeight v = 1 := by
  have h := fejer_exact 1 (by norm_num)
  norm_num at h ⊢
  exact h

lemma fejerNode_mem (v : ℕ) : fejerNode v ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

lemma fejer_exact_monomial (k : ℕ) (hk : k < 256) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, (x:ℂ)^k) := by
  have h := fejer_exact (Polynomial.X^k) (by simpa using hk)
  simp only [eval_pow,eval_X] at h
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [← Complex.ofReal_pow,intervalIntegral.integral_ofReal] using hc

lemma fejer_exact_complex (c : ℕ → ℂ) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*
      (∑ k ∈ Finset.range 256, c k*(fejerNode v : ℂ)^k)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, ∑ k ∈ Finset.range 256, c k*(x:ℂ)^k) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ∑ v ∈ Finset.range 256,
          (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [fejer_exact_monomial k (Finset.mem_range.mp hk)]; ring
  · intro k hk
    exact Continuous.intervalIntegrable (by fun_prop) _ _

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar

lemma geometric_tail_error {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
    (ha : HasSum a v) (hr0 : 0 ≤ r) (hr : r < 1)
    (hb : ∀ n, ‖a n‖ ≤ M*r^n) (N : ℕ) :
    ‖v-∑ n ∈ Finset.range N, a n‖ ≤ M*r^N/(1-r) := by
  have hsum := ha.summable.sum_add_tsum_nat_add N
  rw [ha.tsum_eq] at hsum
  have he : v-∑ n ∈ Finset.range N, a n = ∑' n, a (n+N) := by
    rw [← hsum]
    abel
  rw [he]
  have hg : HasSum (fun n : ℕ => M*r^N*r^n) (M*r^N/(1-r)) :=
    (hasSum_geometric_of_lt_one hr0 hr).mul_left (M*r^N)
  apply tsum_of_norm_bounded hg
  intro n
  calc
    ‖a (n+N)‖ ≤ M*r^(n+N) := hb _
    _ = M*r^N*r^n := by rw [pow_add]; ring

noncomputable def taylorPolynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹*iteratedDeriv n f c*(z-c)^n

lemma analytic_taylor_error {f : ℂ → ℂ} {c z : ℂ} {R M r : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hbound : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : ‖z-c‖ ≤ r*R) (N : ℕ) :
    ‖f z-taylorPolynomial f c N z‖ ≤ M*r^N/(1-r) := by
  have hz' : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hz.trans_lt (by nlinarith)
  have hsum := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hz'
  have hs : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹*
      iteratedDeriv n f c*(z-c)^n) (f z) := by
    convert hsum using 1
    all_goals first | rfl | (funext n; simp only [smul_eq_mul]; ring)
  apply geometric_tail_error hs hr0 hr _ N
  intro n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf hbound
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f c‖ * ‖z-c‖^n ≤
      (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ)*M/R^n) * (r*R)^n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity))
        (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity) (by positivity)
    _ = M*r^n := by rw [mul_pow]; field_simp


lemma positive_quadrature_error {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (w t : ι → ℝ) (f p : ℝ → ℂ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, t i ∈ Icc a b)
    (hmass : ∑ i, w i = b-a)
    (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (herr : ∀ x ∈ Icc a b, ‖f x-p x‖ ≤ ε)
    (hexact : (∫ x in a..b, p x) = ∑ i, (w i : ℂ)*p (t i)) :
    ‖(∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i)‖ ≤ 2*(b-a)*ε := by
  have hi₁ : IntervalIntegrable f volume a b :=
    (hf.intervalIntegrable_of_Icc hab)
  have hi₂ : IntervalIntegrable p volume a b :=
    (hp.intervalIntegrable_of_Icc hab)
  have he : (∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i) =
      (∫ x in a..b, f x-p x) - ∑ i, (w i : ℂ)*(f (t i)-p (t i)) := by
    rw [intervalIntegral.integral_sub hi₁ hi₂, hexact]
    simp only [mul_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  have hInt : ‖∫ x in a..b, f x-p x‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∫ x in a..b, ‖f x-p x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, ε := intervalIntegral.integral_mono_on hab
        (hi₁.sub hi₂).norm (intervalIntegrable_const) (fun x hx => herr x hx)
      _ = (b-a)*ε := by simp
  have hFin : ‖∑ i, (w i : ℂ)*(f (t i)-p (t i))‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∑ i, ‖(w i : ℂ)*(f (t i)-p (t i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, w i*ε := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (herr _ (ht i)) (hw i)
      _ = (b-a)*ε := by rw [← Finset.sum_mul, hmass]
  exact (norm_sub_le _ _).trans (by nlinarith)

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma taylorPolynomial_zero (f : ℂ → ℂ) (N : ℕ) :
    taylorPolynomial f 0 N = fun z =>
      ∑ k ∈ Finset.range N, ((k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)*z^k := by
  funext z
  simp only [taylorPolynomial,sub_zero]

lemma fejer_analytic_average_error (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 2))
    (hbound : ∀ z ∈ Metric.sphere 0 2, ‖f z‖ ≤ (10:ℝ)^53) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val)‖ < 1/10^22 := by
  let p : ℝ → ℂ := fun x => taylorPolynomial f 0 256 x
  let ε : ℝ := (10:ℝ)^53*(1/2:ℝ)^256/(1-(1/2:ℝ))
  have hb (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
      ‖f x-p x‖ ≤ ε := by
    apply analytic_taylor_error (by norm_num : (0:ℝ)<2) (by positivity)
      (by norm_num : (0:ℝ)≤1/2) (by norm_num) hf hbound _ 256
    simp only [sub_zero,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hp : Continuous p := by
    unfold p
    simp only [taylorPolynomial_zero]
    fun_prop
  have hc : ContinuousOn (fun x : ℝ => f x) (Icc (-1:ℝ) 1) := by
    apply hf.continuousOn.comp (Complex.continuous_ofReal.continuousOn)
    intro x hx
    apply subset_closure
    rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    have := abs_le.mpr hx
    linarith
  have hw (v : Fin 256) : 0 ≤ 2*fejerWeight v.val := by
    have := fejerWeight_pos v.val
    positivity
  have hmass : (∑ v : Fin 256, 2*fejerWeight v.val) = (1:ℝ)-(-1) := by
    rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range,fejer_mass]
    norm_num
  have hexact : (∫ x in (-1:ℝ)..1, p x) =
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*p (fejerNode v.val) := by
    have hh : (∑ v ∈ Finset.range 256, (fejerWeight v:ℂ)*p (fejerNode v)) =
        (1/2:ℂ)*(∫ x in (-1:ℝ)..1, p x) := by
      simpa only [p,taylorPolynomial,sub_zero] using
        fejer_exact_complex (fun k => (k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)
    rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => ((2*fejerWeight v:ℝ):ℂ)*p (fejerNode v)) 256]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc,← Finset.mul_sum]
    rw [hh]
    ring
  have he := positive_quadrature_error (-1) 1 (by norm_num)
    (fun v : Fin 256 => 2*fejerWeight v.val) (fun v : Fin 256 => fejerNode v.val)
    (fun x : ℝ => f x) p ε hw (fun v => fejerNode_mem v.val) hmass hc hp.continuousOn hb hexact
  have heq : (1/2:ℂ)*((∫ x in (-1:ℝ)..1, f x)-
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*f (fejerNode v.val)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x)-
        ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val) := by
    simp only [mul_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(2*(1-(-1))*ε) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ < 1/10^22 := by norm_num [ε]

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def diskAffine (j : ℕ) (w : ℂ) : ℂ := (diskCenter j:ℂ)+w/12
lemma diskAffine_mem {j : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖diskAffine j w-(diskCenter j:ℂ)‖ ≤ 1/6 := by
  simp only [diskAffine,add_sub_cancel_left,norm_div,Complex.norm_ofNat]
  linarith

lemma finiteDensity_differentiable (c d : ℕ → ℝ) (j : ℕ) :
    Differentiable ℂ (finiteDensity c d j) := by
  unfold finiteDensity complexU complexV
  fun_prop
lemma complexDirectFactor_differentiable (m y : ℝ) (ell : ℕ) :
    Differentiable ℂ (complexDirectFactor m y ell) := by
  unfold complexDirectFactor
  fun_prop
lemma complexLambda_differentiableAt {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexLambda t := by
  unfold complexLambda
  fun_prop (disch := exact mul_ne_zero (Complex.ofReal_ne_zero.mpr b_pos.ne') ht)
lemma complexZ_differentiableAt {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexZ t := by
  unfold complexZ
  fun_prop (disch := exact ht)
lemma complexTransformedFactor_differentiableAt {t : ℂ}
    (ht : t+Complex.I*(h:ℂ) ≠ 0) (m y : ℝ) (ell : ℕ) :
    DifferentiableAt ℂ (complexTransformedFactor m y ell) t := by
  have hL := complexLambda_differentiableAt ht
  have hZ := complexZ_differentiableAt ht
  unfold complexTransformedFactor
  fun_prop

lemma directIntegrand_analytic (c d : ℕ → ℝ) (j : ℕ) (m y : ℝ) (ell : ℕ) :
    DiffContOnCl ℂ (fun w => finiteDensity c d j (diskAffine j w) *
      complexDirectFactor m y ell (diskAffine j w)) (Metric.ball 0 2) := by
  apply Differentiable.diffContOnCl
  have hA : Differentiable ℂ (diskAffine j) := by unfold diskAffine; fun_prop
  exact ((finiteDensity_differentiable c d j).comp hA).mul
    ((complexDirectFactor_differentiable m y ell).comp hA)

lemma transformedIntegrand_analytic (c d : ℕ → ℝ) {j : ℕ} (hj : j < 6) (m y : ℝ) (ell : ℕ) :
    DiffContOnCl ℂ (fun w => finiteDensity c d j (diskAffine j w) *
      complexTransformedFactor m y ell (diskAffine j w)) (Metric.ball 0 2) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hw' : ‖w‖ ≤ 2 := by
    rw [closure_ball (0:ℂ) (by norm_num : (2:ℝ) ≠ 0),Metric.mem_closedBall,dist_zero_right] at hw
    exact hw
  have ht := disk_denominator_ne hj (diskAffine_mem hw')
  have hA : DifferentiableAt ℂ (diskAffine j) w := by unfold diskAffine; fun_prop
  exact (((finiteDensity_differentiable c d j).differentiableAt.comp w hA).mul
    ((complexTransformedFactor_differentiableAt ht m y ell).comp w hA)).differentiableWithinAt

lemma directMoment_piece_average_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
        complexDirectFactor m y ell (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
          complexDirectFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22 := by
  apply fejer_analytic_average_error _ (directIntegrand_analytic c d j m y ell)
  intro w hw'
  apply directIntegrand_disk_bound c d hw hj (diskAffine_mem ?_) hm0 hm1 hy ell
  simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hw'

lemma transformedMoment_piece_average_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
        complexTransformedFactor m y ell (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
          complexTransformedFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22 := by
  apply fejer_analytic_average_error _ (transformedIntegrand_analytic c d hj m y ell)
  intro w hw'
  apply transformedIntegrand_disk_bound c d hw hj (diskAffine_mem ?_) hm0 hm1 hy ell
  simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hw'

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def pieceIntegral (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, F t
noncomputable def pieceRule (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  (1/6:ℂ) * ∑ v : Fin 256, (fejerWeight v.val:ℂ) *
    F (diskAffine j (fejerNode v.val))

lemma pieceIntegral_affine (F : ℂ → ℂ) (j : ℕ) :
    pieceIntegral F j = (1/12:ℂ) * ∫ x in (-1:ℝ)..1,
      F (diskAffine j x) := by
  have he := intervalIntegral.smul_integral_comp_add_mul (fun x : ℝ => F x)
    (a := -1) (b := 1) (1/12) (diskCenter j)
  have ha : diskCenter j + (1/12:ℝ)*(-1) = (j:ℝ)/6 := by
    unfold diskCenter; ring
  have hb : diskCenter j + (1/12:ℝ)*1 = ((j:ℝ)+1)/6 := by
    unfold diskCenter; ring
  rw [ha,hb] at he
  have hint : (fun x : ℝ => F (diskAffine j x)) =
      (fun x : ℝ => F ((diskCenter j + (1/12:ℝ)*x : ℝ):ℂ)) := by
    funext x
    congr 1
    simp only [diskAffine,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  rw [pieceIntegral,hint,← he]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]

lemma piece_rule_error_scaling (F : ℂ → ℂ) (j : ℕ) {ε : ℝ}
    (he : ‖(1/2:ℂ) * (∫ x in (-1:ℝ)..1, F (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        F (diskAffine j (fejerNode v.val))‖ < ε) :
    ‖pieceIntegral F j-pieceRule F j‖ < ε/6 := by
  rw [pieceIntegral_affine,pieceRule]
  have hid (a b : ℂ) : (1/12:ℂ)*a-(1/6:ℂ)*b =
      (1/6:ℂ)*((1/2:ℂ)*a-b) := by ring
  rw [hid,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
  linarith

lemma directMoment_piece_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖pieceIntegral (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j-
      pieceRule (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j‖ <
        (1/10^22)/6 :=
  piece_rule_error_scaling _ _ (directMoment_piece_average_error c d hw hj hm0 hm1 hy ell)

lemma transformedMoment_piece_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖pieceIntegral (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j-
      pieceRule (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ <
        (1/10^22)/6 :=
  piece_rule_error_scaling _ _ (transformedMoment_piece_average_error c d hw hj hm0 hm1 hy ell)

lemma six_piece_error {F G : Fin 6 → ℂ} {ε : ℝ}
    (he : ∀ j, ‖F j-G j‖ < ε/6) : ‖(∑ j, F j)-(∑ j, G j)‖ < ε := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans_lt ?_
  have hs : ∑ j : Fin 6, ‖F j-G j‖ < ∑ j : Fin 6, ε/6 :=
    Finset.sum_lt_sum (by intro j _; exact (he j).le)
      ⟨0,Finset.mem_univ _,he 0⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  linarith

lemma directMoment_rule_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(∑ j : Fin 6, pieceIntegral
        (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j)-
      ∑ j : Fin 6, pieceRule
        (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j‖ < 1/10^22 :=
  six_piece_error (fun j => directMoment_piece_error c d hw j.isLt hm0 hm1 hy ell)

lemma transformedMoment_rule_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(∑ j : Fin 6, pieceIntegral
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j)-
      ∑ j : Fin 6, pieceRule
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ < 1/10^22 :=
  six_piece_error (fun j => transformedMoment_piece_error c d hw j.isLt hm0 hm1 hy ell)

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def singleCoefficient (n : ℕ) (k : ℕ) : ℝ := if k=n then 1 else 0
lemma singleCoefficient_mass {n : ℕ} (hn : n ≤ 100) :
    ∑ k ∈ Finset.range 101, |singleCoefficient n k| = 1 := by
  simp [singleCoefficient, apply_ite, show n < 101 by omega]
lemma singleDensity_u {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (singleCoefficient n) (fun _ => 0) j t = complexU n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]
lemma singleDensity_v {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (fun _ => 0) (singleCoefficient n) j t = complexV n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]

noncomputable def complexBasis (d : Bool) (n j : ℕ) (t : ℂ) : ℂ :=
  if d then complexV n j t else complexU n j t
noncomputable def complexBasisMoment (d e : Bool) (n j m : ℕ) (t : ℂ) : ℂ :=
  complexBasis d n j t * complexTransformedFactor m 1 (if e then 1 else 0) t

lemma complexBasis_rule_error {n m : ℕ} (hn : n ≤ 100) (hm : m ≤ 100) (d e : Bool) :
    ‖(∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n j.val m) j.val)-
      ∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val‖ < 1/10^22 := by
  have hw1 : ∑ k ∈ Finset.range 101, (|singleCoefficient n k|+|(0:ℝ)|) ≤ 3 := by
    simp only [abs_zero,add_zero,singleCoefficient_mass hn]; norm_num
  have hw2 : ∑ k ∈ Finset.range 101, (|(0:ℝ)|+|singleCoefficient n k|) ≤ 3 := by
    simp only [abs_zero,zero_add,singleCoefficient_mass hn]; norm_num
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm1 : (m:ℝ) ≤ 100 := by exact_mod_cast hm
  unfold complexBasisMoment complexBasis
  cases d
  · simpa only [singleDensity_u hn,Bool.false_eq_true,ite_false]
      using transformedMoment_rule_error (singleCoefficient n) (fun _ => 0) hw1
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)
  · simpa only [singleDensity_v hn,ite_true]
      using transformedMoment_rule_error (fun _ => 0) (singleCoefficient n) hw2
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)

end SharpPlanar


end OAI

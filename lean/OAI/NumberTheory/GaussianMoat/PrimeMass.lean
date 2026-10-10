import OAI.NumberTheory.GaussianMoat.ResidueQuotient

namespace OAI

namespace GaussianMoat

open Filter Topology Finset
namespace PrimeLogMass
open ArithmeticFunction.vonMangoldt Complex

lemma residue_real_series {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  refine ofReal_injective ?_
  simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
    ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx,
    eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
    LSeries, LSeries.term]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
  · rfl

theorem residue_moment_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {j : ℝ} (hj : 0 < j) :
    Tendsto (fun X : ℝ => (∑' n, residueClass a n / (n : ℝ) ^ (1+j/X)) / X)
      atTop (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
  have hinv : Tendsto (fun X : ℝ => j/X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have harg : Tendsto (fun X : ℝ => ((1+j/X : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hr : Tendsto (fun X : ℝ => 1+j/X) atTop (𝓝 1) := by
      simpa using hinv.const_add 1
    simpa only [Function.comp_def,ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hmem : ∀ᶠ X : ℝ in atTop, ((1+j/X : ℝ) : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    change 1 ≤ 1+j/X
    exact le_add_of_nonneg_right (div_nonneg hj.le hX.le)
  have hc : Tendsto (fun X : ℝ => (LFunctionResidueClassAux a ((1+j/X : ℝ) : ℂ)).re)
      atTop (𝓝 (LFunctionResidueClassAux a 1).re) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((continuousOn_LFunctionResidueClassAux a 1 (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨harg,hmem⟩))
  have hz := hc.div_atTop tendsto_id
  have hl : Tendsto (fun X : ℝ => (LFunctionResidueClassAux a ((1+j/X : ℝ) : ℂ)).re / X +
      (q.totient : ℝ)⁻¹ / j) atTop (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
    simpa using hz.add_const ((q.totient : ℝ)⁻¹ / j)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [residue_real_series ha (by linarith [div_pos hj hX] : 1 < 1+j/X)]
  rw [add_div,add_sub_cancel_left,div_div,div_mul_cancel₀ _ hX.ne']

open intervalIntegral MeasureTheory

noncomputable def betaMoment (m n : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, x^m*(1-x)^n

lemma betaMoment_pos (m n : ℕ) : 0 < betaMoment m n := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous (fun x : ℝ => x^m*(1-x)^n)).intervalIntegrable _ _
  · intro x hx
    exact mul_pos (pow_pos hx.1 _) (pow_pos (sub_pos.mpr hx.2) _)
  · norm_num

lemma betaMoment_succ (m n : ℕ) :
    betaMoment (m+1) n = (m+1 : ℝ)/(m+n+2)*betaMoment m n := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^(m+1)*(1-x)^(n+1))
      ((m+1 : ℝ)*x^m*(1-x)^(n+1) - (n+1 : ℝ)*x^(m+1)*(1-x)^n) x := by
    have h1 : HasDerivAt (fun y : ℝ => y^(m+1)) ((m+1 : ℝ)*x^m) x := by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hasDerivAt_pow (m+1) x
    have h2 : HasDerivAt (fun y : ℝ => (1-y)^(n+1)) (-(n+1 : ℝ)*(1-x)^n) x := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq, sub_zero, zero_sub,
        mul_neg_one, neg_mul] using! ((hasDerivAt_id x).const_sub 1).pow (n+1)
    convert! h1.mul h2 using 1; ring
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      (m+1 : ℝ)*x^m*(1-x)^(n+1)-(n+1 : ℝ)*x^(m+1)*(1-x)^n)).intervalIntegrable 0 1)
  have hsplit : betaMoment m (n+1)+betaMoment (m+1) n = betaMoment m n := by
    unfold betaMoment
    rw [← intervalIntegral.integral_add]
    · congr 1
      funext x
      rw [pow_succ,pow_succ]
      ring
    · exact (by fun_prop : Continuous (fun x : ℝ => x^m*(1-x)^(n+1))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ => x^(m+1)*(1-x)^n)).intervalIntegrable _ _
  have hi (u v : ℕ) : IntervalIntegrable (fun x : ℝ => x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hmul (c : ℝ) (u v : ℕ) :
      (∫ x : ℝ in 0..1, c*x^u*(1-x)^v) = c*betaMoment u v := by
    simp only [mul_assoc,intervalIntegral.integral_const_mul,betaMoment]
  rw [intervalIntegral.integral_sub
    (by simpa only [mul_assoc] using (hi m (n+1)).const_mul (m+1 : ℝ))
    (by simpa only [mul_assoc] using (hi (m+1) n).const_mul (n+1 : ℝ)),
    hmul,hmul] at hInt
  simp only [one_pow,sub_self,zero_pow (Nat.succ_ne_zero _),mul_zero,zero_mul,sub_zero] at hInt
  have hn : (0 : ℝ) < m+n+2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn.ne').mpr
  nlinarith

noncomputable def windowPolynomialAux (m n : ℕ) : Polynomial ℝ :=
  Polynomial.X^m*(1-Polynomial.X)^n*
    ((Polynomial.X-Polynomial.C (7/20))*(Polynomial.C (11/30)-Polynomial.X))

lemma windowPolynomialAux_eval (m n : ℕ) (y : ℝ) :
    Polynomial.eval y (windowPolynomialAux m n) = y^m*(1-y)^n*((y-7/20)*(11/30-y)) := by
  simp only [windowPolynomialAux,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C]

noncomputable def windowPolynomial : Polynomial ℝ := windowPolynomialAux 1431 2567

lemma windowPolynomial_eval (y : ℝ) :
    Polynomial.eval y windowPolynomial = y^1431*(1-y)^2567*((y-7/20)*(11/30-y)) :=
  windowPolynomialAux_eval 1431 2567 y

lemma windowPolynomial_nonpos {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hout : y ≤ 7/20 ∨ 11/30 ≤ y) : Polynomial.eval y windowPolynomial ≤ 0 := by
  rw [windowPolynomial_eval]
  have hp : 0 ≤ y^1431*(1-y)^2567 := mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg (sub_nonneg.mpr hy.2) _)
  apply mul_nonpos_of_nonneg_of_nonpos hp
  rcases hout with hl | hr
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hl]) (by linarith only [hl])
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hr]) (by linarith only [hr])

lemma betaMoment_quadratic (m n : ℕ) (a b : ℝ) :
    (∫ x : ℝ in 0..1, x^m*(1-x)^n*((x-a)*(b-x))) =
      (a+b)*betaMoment (m+1) n-betaMoment (m+2) n-a*b*betaMoment m n := by
  have he : (fun x : ℝ => x^m*(1-x)^n*((x-a)*(b-x))) = fun x =>
      (a+b)*(x^(m+1)*(1-x)^n)-(x^(m+2)*(1-x)^n)-a*b*(x^m*(1-x)^n) := by
    funext x
    simp only [pow_add,pow_one,pow_two]
    ring
  have hi (u v : ℕ) : IntervalIntegrable (fun x : ℝ => x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_sub ((hi (m+1) n).const_mul _ |>.sub (hi (m+2) n))
    ((hi m n).const_mul _),
    intervalIntegral.integral_sub ((hi (m+1) n).const_mul _) (hi (m+2) n),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  rfl

lemma windowPolynomial_integral_pos : 0 < ∫ x : ℝ in 0..1, Polynomial.eval x windowPolynomial := by
  simp only [windowPolynomial_eval]
  rw [betaMoment_quadratic]
  change 0 < (7/20+11/30)*betaMoment 1432 2567 - betaMoment 1433 2567 -
    (7/20*(11/30))*betaMoment 1431 2567
  rw [betaMoment_succ 1432 2567, betaMoment_succ 1431 2567]
  norm_num only [Nat.cast_ofNat]
  have hp := betaMoment_pos 1431 2567
  nlinarith

lemma polynomial_integral_coeff (P : Polynomial ℝ) :
    (∫ x : ℝ in 0..1, P.eval x) = ∑ j ∈ P.support, P.coeff j / (j+1 : ℝ) := by
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,integral_pow,one_pow,
      zero_pow (Nat.succ_ne_zero _),sub_zero,mul_one_div]
  · intro j _
    exact (by fun_prop : Continuous (fun x : ℝ => P.coeff j*x^j)).intervalIntegrable _ _

theorem residue_polynomial_moment_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (P : Polynomial ℝ) :
    Tendsto (fun X : ℝ => ∑ j ∈ P.support, P.coeff j *
      ((∑' n, residueClass a n / (n : ℝ) ^ (1+(j+1 : ℝ)/X)) / X)) atTop
      (𝓝 ((q.totient : ℝ)⁻¹ * (∫ x : ℝ in 0..1, P.eval x))) := by
  have h (j : ℕ) := (residue_moment_limit ha (show (0 : ℝ) < j+1 by positivity)).const_mul (P.coeff j)
  have hs := tendsto_finsetSum P.support (fun j _ => h j)
  convert hs using 1
  congr 1
  rw [polynomial_integral_coeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma residue_summable {q : ℕ} [NeZero q] (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => residueClass a n / (n : ℝ)^x) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))

lemma laplace_power (n j : ℕ) (X : ℝ) (hn : n ≠ 0) :
    (n : ℝ) ^ (-(j+1 : ℝ)/X) =
      (Real.exp (-Real.log n / X))^(j+1) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn), ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma laplace_term {q : ℕ} [NeZero q] (a : ZMod q) (n j : ℕ) (X : ℝ) :
    residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X) =
      residueClass a n / n * (Real.exp (-Real.log n/X))^(j+1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [Real.rpow_add (by exact_mod_cast hn),Real.rpow_one,div_mul_eq_div_div,
      div_eq_mul_inv _ ((n : ℝ)^((j+1 : ℝ)/X)), ← Real.rpow_neg (by positivity),
      show -((j+1 : ℝ)/X) = -(j+1 : ℝ)/X by ring,laplace_power n j X (by omega)]

lemma polynomial_laplace_series {q : ℕ} [NeZero q] (a : ZMod q)
    (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X) :
    (∑ j ∈ P.support, P.coeff j *
      (∑' n, residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X))) =
    ∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P := by
  have hs (j : ℕ) : Summable (fun n : ℕ => residueClass a n /
      (n : ℝ)^(1+(j+1 : ℝ)/X)) := residue_summable a (by
    have : 0 < (j+1 : ℝ)/X := div_pos (by positivity) hX
    linarith)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (P.coeff j))]
  apply tsum_congr
  intro n
  simp_rw [laplace_term,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma polynomial_laplace_summable {q : ℕ} [NeZero q] (a : ZMod q)
    (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℕ => residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P) := by
  have hs (j : ℕ) : Summable (fun n : ℕ => P.coeff j * (residueClass a n /
      (n : ℝ)^(1+(j+1 : ℝ)/X))) := (residue_summable a (by
    have : 0 < (j+1 : ℝ)/X := div_pos (by positivity) hX
    linarith)).mul_left _
  apply (summable_sum (s := P.support) (fun j _ => hs j)).congr
  intro n
  simp_rw [laplace_term,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma windowPolynomial_le_one {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Polynomial.eval y windowPolynomial ≤ 1 := by
  by_cases hl : y ≤ 7/20
  · exact (windowPolynomial_nonpos hy (.inl hl)).trans (by norm_num)
  by_cases hr : 11/30 ≤ y
  · exact (windowPolynomial_nonpos hy (.inr hr)).trans (by norm_num)
  rw [windowPolynomial_eval]
  have h1 : 0 ≤ y^1431 := pow_nonneg hy.1 _
  have h2 : 0 ≤ (1-y)^2567 := pow_nonneg (by linarith only [hy.2]) _
  have he : y^1431*(1-y)^2567 ≤ 1 :=
    (mul_le_of_le_one_left h2 (pow_le_one₀ hy.1 hy.2)).trans
      (pow_le_one₀ (by linarith only [hy.2]) (by linarith only [hy.1]))
  have hf : (y-7/20)*(11/30-y) ≤ 1 :=
    (mul_le_of_le_one_left (by linarith only [hr]) (by linarith only [hy.2])).trans
      (by linarith only [hy.1])
  exact (mul_le_of_le_one_left
    (mul_nonneg (by linarith only [hl]) (by linarith only [hr])) he).trans hf

lemma exp_window_lower : Real.exp (-(10499/10000 : ℝ)) < 7/20 := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 499/10000)
  have he := Real.exp_one_gt_d9
  have hp : Real.exp (10499/10000 : ℝ) = Real.exp 1 * Real.exp (499/10000 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,hp]
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

lemma exp_window_upper : (11/30 : ℝ) < Real.exp (-(1001/1000 : ℝ)) := by
  have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/1000)
    (by norm_num : (1/1000 : ℝ) < 1)
  have hp : Real.exp (1001/1000 : ℝ) = Real.exp 1 * Real.exp (1/1000 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,inv_eq_one_div]
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  rw [hp]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
  norm_num at hm
  nlinarith [Real.exp_one_lt_d9]

noncomputable def windowIndices (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊Real.exp (10499/10000*X)⌋₊+1)).filter (fun n => Real.exp (1001/1000*X) ≤ n)

lemma mem_windowIndices (X : ℝ) (n : ℕ) :
    n ∈ windowIndices X ↔ Real.exp (1001/1000*X) ≤ n ∧ (n : ℝ) ≤ Real.exp (10499/10000*X) := by
  simp only [windowIndices,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.exp_pos _).le,and_comm]

lemma laplace_window_nonpos {X : ℝ} (hX : 0 < X) (n : ℕ)
    (hn : n ≠ 0) (hout : n ∉ windowIndices X) :
    Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial ≤ 0 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  apply windowPolynomial_nonpos
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  rw [mem_windowIndices,not_and_or] at hout
  rcases hout with hl | hr
  · right
    have : Real.log n < 1001/1000*X := (Real.log_lt_iff_lt_exp hnp).mpr (lt_of_not_ge hl)
    apply exp_window_upper.le.trans
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hX).mpr
    linarith
  · left
    have : 10499/10000*X < Real.log n := (Real.lt_log_iff_exp_lt hnp).mpr (lt_of_not_ge hr)
    apply le_trans _ exp_window_lower.le
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hX).mpr
    linarith

lemma window_mass_dominates {q : ℕ} [NeZero q] (a : ZMod q) {X : ℝ} (hX : 0 < X) :
    (∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) ≤
      ∑ n ∈ windowIndices X, residueClass a n / n := by
  classical
  let f := fun n : ℕ => if n ∈ windowIndices X then residueClass a n / n else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := windowIndices X) (by
    intro n hn
    simp [f,hn])
  have ht : (∑' n, f n) = ∑ n ∈ windowIndices X, residueClass a n / n := by
    rw [tsum_eq_sum (s := windowIndices X) (by intro n hn; simp [f,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f,hn]
  rw [← ht]
  apply Summable.tsum_le_tsum _ (polynomial_laplace_summable a windowPolynomial hX) hf
  intro n
  by_cases hn : n = 0
  · subst n
    simp [f]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hy : Real.exp (-Real.log n/X) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  have hw : 0 ≤ residueClass a n / n := div_nonneg (residueClass_nonneg a n) (Nat.cast_nonneg n)
  by_cases hm : n ∈ windowIndices X
  · simp only [f,ite_eq_left hm]
    calc
      _ ≤ residueClass a n / n * Real.exp (-Real.log n/X) := by
        exact mul_le_of_le_one_right (mul_nonneg hw hy.1) (windowPolynomial_le_one hy)
      _ ≤ _ := mul_le_of_le_one_right hw hy.2
  · simp only [f,ite_eq_right hm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hw hy.1) (laplace_window_nonpos hX n hn hm)

theorem eventually_residue_window_mass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ windowIndices X, residueClass a n / n := by
  let c := (q.totient : ℝ)⁻¹ * (∫ x : ℝ in 0..1, Polynomial.eval x windowPolynomial)
  have hc : 0 < c := mul_pos (inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero))
    windowPolynomial_integral_pos
  have hlim := residue_polynomial_moment_limit ha windowPolynomial
  have he : ∀ᶠ X : ℝ in atTop,
      c/2 < ∑ j ∈ windowPolynomial.support, windowPolynomial.coeff j *
        ((∑' n, residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X)) / X) :=
    hlim.eventually (eventually_gt_nhds (by dsimp [c]; linarith only [hc] : c/2 < c))
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with X h hX
  have hid := polynomial_laplace_series a windowPolynomial hX
  have h' : c/2 < (∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) / X := by
    rw [← hid,Finset.sum_div]
    simpa only [mul_div_assoc] using h
  exact ((lt_div_iff₀ hX).mp h').le.trans (window_mass_dominates a hX)

theorem eventually_prime_window_mass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ (windowIndices X).filter Nat.Prime, residueClass a n / n := by
  classical
  obtain ⟨c,hc,he⟩ := eventually_residue_window_mass ha
  let f : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass a n) / n
  have hf : Summable f := summable_residueClass_non_primes_div a
  have hn : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; split_ifs <;> positivity [residueClass_nonneg a n]
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_ge_atTop (2*(∑' n, f n)/c)] with X hX hK
  have hb := hf.sum_le_tsum (windowIndices X) (fun n _ => hn n)
  have hid : (∑ n ∈ windowIndices X, residueClass a n/n) =
      (∑ n ∈ (windowIndices X).filter Nat.Prime, residueClass a n/n) +
      ∑ n ∈ windowIndices X, f n := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    split_ifs <;> simp
  rw [hid] at hX
  have hbig := (div_le_iff₀ hc).mp hK
  nlinarith

end PrimeLogMass

theorem irreducible_of_prime_norm {π : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hn : π.norm = (p : ℤ)) : Irreducible π := by
  have hnp : π.norm.natAbs = p := by rw [hn]; simp
  constructor
  · intro hu
    have h := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hnp] at h
    exact hp.ne_one h
  · intro a b hab
    have he : a.norm.natAbs*b.norm.natAbs = p := by
      rw [← Int.natAbs_mul,← Zsqrtd.norm_mul,← hab,hnp]
    have hi : Irreducible p := (Nat.irreducible_iff_nat_prime p).mpr hp
    rcases hi.isUnit_or_isUnit he.symm with ha | hb
    · left
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using ha
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using hb

theorem exists_split_factor {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ π : GaussianInt, Irreducible π ∧ π.norm = (p : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hnp : ¬ Irreducible (p : GaussianInt) := by
    intro hi
    have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mp hi.prime
    omega
  obtain ⟨a,b,hab⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hnp
  have hn : (⟨a,b⟩ : GaussianInt).norm = (p : ℤ) := by
    simp only [Zsqrtd.norm]
    norm_num only [Int.reduceNeg,neg_mul,sub_neg_eq_add]
    have h : (a : ℤ)^2+(b : ℤ)^2 = (p : ℤ) := by exact_mod_cast hab
    simpa only [pow_two,one_mul] using h
  exact ⟨⟨a,b⟩,irreducible_of_prime_norm hp hn,hn⟩

end GaussianMoat

end OAI

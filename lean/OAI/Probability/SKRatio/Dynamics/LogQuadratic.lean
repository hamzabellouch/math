import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SKRatioClock.Clock

noncomputable def logQuadratic : ℝ → ℝ :=
  Function.update (fun x => (Real.log (1+x)-x)/x^2) 0 (-(1/2:ℝ))

lemma logQuadratic_mul_sq (x : ℝ) :
    logQuadratic x*x^2 = Real.log (1+x)-x := by
  classical
  by_cases hx : x=0
  · subst x
    simp [logQuadratic]
  · simp only [logQuadratic, Function.update_of_ne hx]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hx)

lemma continuousAt_logQuadratic : ContinuousAt logQuadratic 0 := by
  classical
  apply continuousAt_update_same.mpr
  have hdom : ∀ᶠ x : ℝ in 𝓝[≠] 0, 0 < 1+x := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (-1:ℝ)<0)).filter_mono nhdsWithin_le_nhds]
      with x hx
    linarith
  have hne : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 := self_mem_nhdsWithin
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun x => 1/(1+x)-1) (g' := fun x => 2*x)
  · filter_upwards [hdom] with x hx
    exact ((hasDerivAt_id x).const_add 1 |>.log hx.ne').sub (hasDerivAt_id x)
  · exact Filter.Eventually.of_forall fun x => by
      convert! (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
      · ext t
        simp [pow_two]
      · simp [two_mul]
  · filter_upwards [hne] with x hx
    exact mul_ne_zero (by norm_num) hx
  · have h : Tendsto (fun x : ℝ => Real.log (1+x)-x) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => Real.log (1+x)-x) 0 := by
        apply ContinuousAt.sub
        · apply ContinuousAt.log
          · fun_prop
          · norm_num
        · fun_prop
      simpa using hc.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun x : ℝ => x^2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · have ht : Tendsto (fun x : ℝ => -1/(2*(1+x))) (𝓝[≠] 0) (𝓝 (-(1/2:ℝ))) := by
      have hc : ContinuousAt (fun x : ℝ => -1/(2*(1+x))) 0 := by
        apply ContinuousAt.div <;> first | fun_prop | norm_num
      convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
    apply ht.congr'
    filter_upwards [hne,hdom] with x hx hd
    field_simp
    ring

noncomputable def poissonMass (m : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-m)*m^k/(k.factorial:ℝ)

lemma poissonMass_stirling {m : ℝ} (hm : 0 < m) {k : ℕ} (hk : 0 < k) :
    Real.sqrt k*poissonMass m k =
      Real.exp ((k:ℝ)*(Real.log (m/k)-(m-k)/k))/
        (Real.sqrt 2*Stirling.stirlingSeq k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have he : Real.exp ((k:ℝ)*(Real.log (m/k)-(m-k)/k)) =
      Real.exp (-m)*(m/(k/Real.exp 1))^k := by
    have ha : (k:ℝ)*(Real.log (m/k)-(m-k)/k) =
        -m+(k:ℝ)*(Real.log (m/k)+1) := by field_simp; ring
    rw [ha, Real.exp_add, Real.exp_nat_mul, Real.exp_add, Real.exp_log (div_pos hm hkp)]
    congr 2
    field_simp
  rw [he]
  unfold poissonMass Stirling.stirlingSeq
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have hs : Real.sqrt (k:ℝ) ≠ 0 := (Real.sqrt_pos.2 hkp).ne'
  have hs2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hx : (k:ℝ)/Real.exp 1 ≠ 0 := div_ne_zero hk0 (Real.exp_ne_zero _)
  rw [div_pow]
  field_simp

theorem poisson_local_limit {k : ℕ → ℕ} {m : ℕ → ℝ} {z : ℝ}
    (hk : Tendsto k atTop atTop) (hm : ∀ᶠ n in atTop, 0 < m n)
    (hd : Tendsto (fun n => (m n-(k n:ℝ))/Real.sqrt (k n)) atTop (𝓝 z)) :
    Tendsto (fun n => Real.sqrt (k n)*poissonMass (m n) (k n)) atTop
      (𝓝 (Real.exp (-(z^2)/2)/(Real.sqrt 2*Real.sqrt Real.pi))) := by
  have hkn : Tendsto (fun n => (k n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hks : Tendsto (fun n => Real.sqrt (k n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hkn
  have hkpos : ∀ᶠ n in atTop, 0 < k n := hk.eventually (eventually_gt_atTop 0)
  have hh : Tendsto (fun n => (m n-(k n:ℝ))/(k n:ℝ)) atTop (𝓝 0) := by
    apply (hd.div_atTop hks).congr'
    filter_upwards [hkpos] with n hn
    have hn0 : (0:ℝ)≤k n := Nat.cast_nonneg _
    rw [div_div, Real.mul_self_sqrt hn0]
  have hq : Tendsto (fun n => logQuadratic ((m n-(k n:ℝ))/(k n:ℝ))) atTop
      (𝓝 (-(1/2:ℝ))) := by
    have h := continuousAt_logQuadratic.tendsto.comp hh
    simpa [Function.comp_def,logQuadratic] using h
  have hprod := hq.mul (hd.pow 2)
  have he : Tendsto (fun n => (k n:ℝ)*(Real.log (m n/k n)-(m n-k n)/k n))
      atTop (𝓝 (-(z^2)/2)) := by
    have ht : (-(1/2:ℝ))*z^2 = -(z^2)/2 := by ring
    rw [ht] at hprod
    apply hprod.congr'
    filter_upwards [hkpos] with n hn
    have hn0 : (k n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsn : Real.sqrt (k n:ℝ)^2 = k n := Real.sq_sqrt (Nat.cast_nonneg _)
    have hlog : 1+(m n-(k n:ℝ))/(k n:ℝ) = m n/k n := by field_simp; ring
    have h := logQuadratic_mul_sq ((m n-(k n:ℝ))/(k n:ℝ))
    rw [hlog] at h
    rw [div_pow,hsn]
    calc
      _ = (k n:ℝ)*(logQuadratic ((m n-(k n:ℝ))/(k n:ℝ))*
        ((m n-(k n:ℝ))/(k n:ℝ))^2) := by field_simp
      _ = _ := by rw [h]
  have hdnom : Tendsto (fun n => Real.sqrt 2*Stirling.stirlingSeq (k n)) atTop
      (𝓝 (Real.sqrt 2*Real.sqrt Real.pi)) :=
    tendsto_const_nhds.mul (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hk)
  have heexp := Real.continuous_exp.continuousAt.tendsto.comp he
  apply (heexp.div hdnom (by positivity)).congr'
  filter_upwards [hm,hkpos] with n hn hnk
  exact (poissonMass_stirling hn hnk).symm

noncomputable def centralIndex (q x : ℝ) (M : ℕ) : ℕ :=
  ⌊q*(M:ℝ)+x*Real.sqrt M⌋₊

lemma center_ratio_tendsto (q x : ℝ) :
    Tendsto (fun n : ℕ => (q*n+x*Real.sqrt n)/(n:ℝ)) atTop (𝓝 q) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h : Tendsto (fun n : ℕ => q+x/Real.sqrt n) atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hs))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp
  nlinarith [congrArg (fun t => x*t) hsq]

lemma center_tendsto_atTop {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n : ℕ => q*n+x*Real.sqrt n) atTop atTop := by
  have h := (center_ratio_tendsto q x).pos_mul_atTop hq
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma centralIndex_atTop {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (centralIndex q x) atTop atTop :=
  tendsto_nat_floor_atTop.comp (center_tendsto_atTop hq x)

lemma centralIndex_deviation {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n => ((centralIndex q x n:ℝ)-q*n)/Real.sqrt n) atTop (𝓝 x) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (fun n : ℕ => 1/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hneg : Tendsto (fun n : ℕ => -(1/Real.sqrt n)) atTop (𝓝 0) := by
    simpa using hzero.neg
  have he : Tendsto (fun n => ((centralIndex q x n:ℝ)-
      (q*n+x*Real.sqrt n))/Real.sqrt n) atTop (𝓝 0) := by
    apply hneg.squeeze' tendsto_const_nhds
    · filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0),
        eventually_gt_atTop 0] with n hn hn0
      have hspos : 0 < Real.sqrt (n:ℝ) := by positivity
      have hh := Nat.lt_floor_add_one (q*n+x*Real.sqrt n)
      change -(1/Real.sqrt (n:ℝ)) ≤ _
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ hspos.le
      dsimp [centralIndex]
      linarith
    · filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0)]
        with n hn
      apply div_nonpos_of_nonpos_of_nonneg _ (Real.sqrt_nonneg _)
      exact sub_nonpos.mpr (Nat.floor_le hn)
  have htt : Tendsto (fun n => (((centralIndex q x n:ℝ)-
      (q*n+x*Real.sqrt n))/Real.sqrt n)+x) atTop (𝓝 x) := by
    simpa using he.add_const x
  apply htt.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma centralIndex_ratio {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n => (centralIndex q x n:ℝ)/(n:ℝ)) atTop (𝓝 q) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun n => q+(((centralIndex q x n:ℝ)-q*n)/Real.sqrt n)/Real.sqrt n)
      atTop (𝓝 q) := by
    simpa using tendsto_const_nhds.add ((centralIndex_deviation hq x).div_atTop hs)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  field_simp
  ring

theorem poisson_scaled_local {q : ℝ} (hq : 0 < q) (x y : ℝ)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hkr : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 q))
    (hkd : Tendsto (fun n => ((k n:ℝ)-q*n)/Real.sqrt n) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*
      poissonMass (q*n+y*Real.sqrt n) (k n)) atTop
      (𝓝 (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)))) := by
  have hratio : Tendsto (fun n => Real.sqrt (k n:ℝ)/Real.sqrt n)
      atTop (𝓝 (Real.sqrt q)) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hkr
    simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using hh
  have hstd : Tendsto (fun n : ℕ => ((q*n+y*Real.sqrt n)-(k n:ℝ))/
      Real.sqrt (k n)) atTop (𝓝 ((y-x)/Real.sqrt q)) := by
    have hh := ((tendsto_const_nhds (x := y)).sub hkd).div hratio
      ((Real.sqrt_pos.2 hq).ne')
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0, hk.eventually (eventually_gt_atTop 0)]
      with n hn hk0
    have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
    have hsk : Real.sqrt (k n:ℝ) ≠ 0 := by positivity
    change (y-((k n:ℝ)-q*n)/Real.sqrt n)/
      (Real.sqrt (k n:ℝ)/Real.sqrt n) = _
    field_simp
    ring
  have hp := poisson_local_limit hk
    ((center_tendsto_atTop hq y).eventually (eventually_gt_atTop 0)) hstd
  have ht := hp.div hratio ((Real.sqrt_pos.2 hq).ne')
  have heconst : (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
      (Real.sqrt 2*Real.sqrt Real.pi))/Real.sqrt q =
      Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)) := by ring
  rw [heconst] at ht
  apply ht.congr'
  filter_upwards [hk.eventually (eventually_gt_atTop 0)] with n hn
  have hsk : Real.sqrt (k n:ℝ) ≠ 0 := by positivity
  change (Real.sqrt (k n:ℝ)*poissonMass _ _)/
    (Real.sqrt (k n:ℝ)/Real.sqrt n) = _
  field_simp

theorem poisson_histogram_pointwise {q : ℝ} (hq : 0 < q) (x y : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*
      poissonMass (q*n+y*Real.sqrt n) (centralIndex q x n)) atTop
      (𝓝 (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)))) :=
  poisson_scaled_local hq x y (centralIndex q x) (centralIndex_atTop hq x)
    (centralIndex_ratio hq x) (centralIndex_deviation hq x)

noncomputable def binomialMass (q : ℝ) (M k : ℕ) : ℝ :=
  (M.choose k:ℝ)*q^k*(1-q)^(M-k)

lemma binomialMass_poisson {q : ℝ} {M k : ℕ} (hk : k ≤ M) (hM : 0 < M) :
    binomialMass q M k =
      poissonMass (q*M) k*poissonMass ((1-q)*M) (M-k)/poissonMass M M := by
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold binomialMass poissonMass
  rw [Nat.cast_choose ℝ hk]
  have he : Real.exp (-(q*(M:ℝ)))*Real.exp (-((1-q)*M)) = Real.exp (-(M:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : (M:ℝ)^k*(M:ℝ)^(M-k) = (M:ℝ)^M := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  simp only [mul_pow]
  have hf1 : (k.factorial:ℝ) ≠ 0 := by positivity
  have hf2 : ((M-k).factorial:ℝ) ≠ 0 := by positivity
  have hf3 : (M.factorial:ℝ) ≠ 0 := by positivity
  have he0 : Real.exp (-(M:ℝ)) ≠ 0 := Real.exp_ne_zero _
  field_simp
  calc
    _ = (M:ℝ)^M * Real.exp (-(M:ℝ)) *q^k*(1-q)^(M-k) := by ring
    _ = _ := by rw [← hp, ← he]; ring

lemma gaussian_formula {q : ℝ} (hq : 0 < q) (x y : ℝ) :
    Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)) =
      gaussianPDFReal y ⟨q,hq.le⟩ x := by
  change _ = (Real.sqrt (2*Real.pi*q))⁻¹ * Real.exp (-(x-y)^2/(2*q))
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) Real.pi_pos.le),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have he : -((y-x)/Real.sqrt q)^2/2 = -(x-y)^2/(2*q) := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  rw [he]
  ring

lemma index_atTop_of_ratio {k : ℕ → ℕ} {q : ℝ} (hq : 0 < q)
    (hkr : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 q)) : Tendsto k atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply (hkr.pos_mul_atTop hq (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma centralIndex_le {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    ∀ᶠ n in atTop, centralIndex q x n ≤ n := by
  filter_upwards [(centralIndex_ratio hql x).eventually (eventually_lt_nhds hqu),
    eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnpos).mp hn
  have hh' : (centralIndex q x n:ℝ) < n := by simpa using hh
  exact le_of_lt (by exact_mod_cast hh')

lemma complementIndex_ratio {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n => ((n-centralIndex q x n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1-q)) := by
  apply ((tendsto_const_nhds (x := (1:ℝ))).sub (centralIndex_ratio hql x)).congr'
  filter_upwards [centralIndex_le hql hqu x,eventually_gt_atTop 0] with n hn hn0
  rw [Nat.cast_sub hn]
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp

lemma complementIndex_deviation {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n => (((n-centralIndex q x n:ℕ):ℝ)-(1-q)*n)/Real.sqrt n)
      atTop (𝓝 (-x)) := by
  apply (centralIndex_deviation hql x).neg.congr'
  filter_upwards [centralIndex_le hql hqu x] with n hn
  rw [Nat.cast_sub hn]
  ring

lemma gaussian_product_quotient {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    gaussianPDFReal 0 ⟨q,hql.le⟩ x *
      gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) /
      gaussianPDFReal 0 1 0 =
    gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x := by
  have hg1 : gaussianPDFReal 0 1 0 = 1/(Real.sqrt 2*Real.sqrt Real.pi) := by
    norm_num [gaussianPDFReal, Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  rw [← gaussian_formula hql x 0, ← gaussian_formula (by linarith : 0 < 1-q) (-x) 0,
    hg1, ← gaussian_formula (mul_pos hql (by linarith : 0 < 1-q)) x 0]
  simp only [zero_sub, neg_div, neg_sq, neg_neg]
  have hq0 : q ≠ 0 := hql.ne'
  have hr0 : 1-q ≠ 0 := by linarith
  have he : -(x/Real.sqrt q)^2/2 + -(x/Real.sqrt (1-q))^2/2 =
      -(x/Real.sqrt (q*(1-q)))^2/2 := by
    simp only [div_pow, Real.sq_sqrt hql.le, Real.sq_sqrt (show 0≤1-q by linarith),
      Real.sq_sqrt (mul_nonneg hql.le (show 0≤1-q by linarith))]
    field_simp
    ring
  rw [mul_div_assoc, div_div, div_mul_div_comm]
  rw [← Real.exp_add]
  simp only [← neg_div]
  rw [he, Real.sqrt_mul hql.le]
  have hs : Real.sqrt q ≠ 0 := by positivity
  have hr : Real.sqrt (1-q) ≠ 0 := by positivity
  have h2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

theorem binomial_histogram_pointwise {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*binomialMass q n (centralIndex q x n)) atTop
      (𝓝 (gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x)) := by
  have ha := poisson_scaled_local hql x 0 (centralIndex q x) (centralIndex_atTop hql x)
    (centralIndex_ratio hql x) (centralIndex_deviation hql x)
  have hb := poisson_scaled_local (by linarith : 0 < 1-q) (-x) 0
    (fun n => n-centralIndex q x n)
    (index_atTop_of_ratio (by linarith) (complementIndex_ratio hql hqu x))
    (complementIndex_ratio hql hqu x) (complementIndex_deviation hql hqu x)
  have hc := poisson_scaled_local (by norm_num : (0:ℝ)<1) 0 0 (fun n => n) tendsto_id
    (by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (div_self (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)).symm)
    (by simp)
  rw [gaussian_formula hql x 0] at ha
  rw [gaussian_formula (by linarith : 0 < 1-q) (-x) 0] at hb
  rw [gaussian_formula (by norm_num : (0:ℝ)<1) 0 0] at hc
  have hc1 : (⟨(1:ℝ),by norm_num⟩ : ℝ≥0) = 1 := by rfl
  rw [hc1] at hc
  have hh := (ha.mul hb).div hc (gaussianPDFReal_pos 0 1 0 (by norm_num)).ne'
  have heq : gaussianPDFReal 0 ⟨q,hql.le⟩ x *
      gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) / gaussianPDFReal 0 1 0 =
      gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x :=
    gaussian_product_quotient hql hqu x
  have hh' : Tendsto (fun n : ℕ =>
      (Real.sqrt (n:ℝ)*poissonMass (q*n+0*Real.sqrt n) (centralIndex q x n))*
      (Real.sqrt (n:ℝ)*poissonMass ((1-q)*n+0*Real.sqrt n) (n-centralIndex q x n))/
      (Real.sqrt (n:ℝ)*poissonMass (1*n+0*Real.sqrt n) n)) atTop
      (𝓝 (gaussianPDFReal 0 ⟨q,hql.le⟩ x *
        gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) / gaussianPDFReal 0 1 0)) := hh
  rw [heq] at hh'
  apply hh'.congr'
  filter_upwards [centralIndex_le hql hqu x,eventually_gt_atTop 0] with n hn hn0
  simp only [zero_mul,add_zero,one_mul]
  rw [binomialMass_poisson hn hn0]
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  field_simp

end SKRatioClock.Clock

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI

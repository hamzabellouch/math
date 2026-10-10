import OAI.InformationTheory.QuantumCircuit.Polynomial

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- Strict exponent gaps absorb every fixed multiplicative constant. -/
lemma eventually_power_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s ≤ (N : ℝ) ^ t := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (t - s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hst)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    C * (N : ℝ) ^ s ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- The same strict gap absorbs a logarithm, with no change to the exponent. -/
lemma eventually_power_log_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s * Real.log N ≤ (N : ℝ) ^ t := by
  have h := ((isLittleO_log_rpow_atTop (sub_pos.2 hst)).const_mul_left C).bound
    (c := 1) zero_lt_one
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : C * Real.log N ≤ (N : ℝ) ^ (t - s) := by
    have hN' : |C * Real.log N| ≤ (N : ℝ) ^ (t - s) := by
      simpa only [Real.norm_eq_abs, one_mul,
        abs_of_nonneg (Real.rpow_nonneg hN0.le (t - s))] using hN
    exact (le_abs_self _).trans hN'
  calc
    C * (N : ℝ) ^ s * Real.log N = (C * Real.log N) * (N : ℝ) ^ s := by ring
    _ ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

lemma ceil_rpow_bounds {N : ℕ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    (N : ℝ) ^ a ≤ (⌈(N : ℝ) ^ a⌉₊ : ℝ) ∧
    (⌈(N : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ a := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow h1 ha
  constructor
  · exact Nat.le_ceil _
  · have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) a)
    linarith

lemma ceil_rpow_log {N : ℕ} {b : ℝ} (hN : 2 ≤ N) (hb : 0 ≤ b) :
    Real.log (⌈(N : ℝ) ^ b⌉₊ : ℝ) ≤ (b + 1) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hbounds := ceil_rpow_bounds (show 1 ≤ N by omega) hb
  have hceil0 : (0 : ℝ) < ⌈(N : ℝ) ^ b⌉₊ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hbounds.1
  calc
    _ ≤ Real.log (2 * (N : ℝ) ^ b) := Real.log_le_log hceil0 hbounds.2
    _ = Real.log 2 + b * Real.log N := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hN0 _)),
        Real.log_rpow hN0]
    _ ≤ (b + 1) * Real.log N := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
      nlinarith


lemma approx_weight_exp {N r k : ℕ} {v u : ℝ} (hN : 6 ≤ N)
    (hsum : (r : ℝ) + k ≤ 4 * (N : ℝ) ^ v)
    (hcostN : 8 * (N : ℝ) ^ v * Real.log N ≤ (N : ℝ) ^ u) :
    (1 + (N : ℝ)) ^ r * (7 + 4 * (N : ℝ)) ^ k ≤ Real.exp ((N : ℝ) ^ u) := by
  have hN6R : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + (N : ℝ)) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : 0 < 1 + (N : ℝ))
      (show 1 + (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith only [hN6R])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlog2 : Real.log (7 + 4 * (N : ℝ)) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : 0 < 7 + 4 * (N : ℝ))
      (show 7 + 4 * (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith only [hN6R])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hcost : (r : ℝ) * Real.log (1 + (N : ℝ)) +
      (k : ℝ) * Real.log (7 + 4 * (N : ℝ)) ≤ (N : ℝ) ^ u := by
    calc
      _ ≤ (r : ℝ) * (2 * Real.log N) + (k : ℝ) * (2 * Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg r))
          (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k))
      _ ≤ 8 * (N : ℝ) ^ v * Real.log N := by
        nlinarith only [mul_le_mul_of_nonneg_right hsum hlogN]
      _ ≤ _ := hcostN
  calc
    _ = Real.exp ((r : ℝ) * Real.log (1 + (N : ℝ)) +
        (k : ℝ) * Real.log (7 + 4 * (N : ℝ))) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by positivity), Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.2 hcost

lemma approx_decay_exp {r : ℕ} {m z : ℝ} (hr : 1 ≤ r) (hm : 1 ≤ Real.log m)
    (hz : z ≤ r) : 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) ≤ Real.exp (-z) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  calc
    _ ≤ Real.exp 1 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      have := Real.add_one_le_exp 1
      norm_num at this ⊢
      exact this
    _ = Real.exp (1 - 3 * (r : ℝ) * Real.log m) := by rw [← Real.exp_add]; congr 1
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      nlinarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg r), hz, hr1]

lemma ceil_approx_condition {N : ℕ} {a b v : ℝ} (hN : 2 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (hkN : (8 * (b + 1)) * (N : ℝ) ^ ((a + b) / 2) * Real.log N ≤ (N : ℝ) ^ v) :
    4 * (⌈(N : ℝ) ^ a⌉₊ : ℝ) * Real.log (⌈(N : ℝ) ^ b⌉₊ : ℝ) ≤
      (⌈(N : ℝ) ^ v⌉₊ : ℝ) *
        Real.sqrt ((⌈(N : ℝ) ^ a⌉₊ : ℝ) / (⌈(N : ℝ) ^ b⌉₊ : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let r := ⌈(N : ℝ) ^ a⌉₊
  let m := ⌈(N : ℝ) ^ b⌉₊
  let k := ⌈(N : ℝ) ^ v⌉₊
  have hrap := ceil_rpow_bounds hN1 ha
  have hmbp := ceil_rpow_bounds hN1 hb
  have hkvp := ceil_rpow_bounds hN1 hv
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hmbp.1
  have hlogm := ceil_rpow_log hN hb
  have hsquare : ((N : ℝ) ^ ((a + b) / 2)) ^ 2 = (N : ℝ) ^ a * (N : ℝ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    ring
  have hsqrt : Real.sqrt ((r : ℝ) * m) ≤ 2 * (N : ℝ) ^ ((a + b) / 2) := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hmul := mul_le_mul hrap.2 hmbp.2 (Nat.cast_nonneg m)
      (by positivity : 0 ≤ 2 * (N : ℝ) ^ a)
    rw [mul_pow, hsquare]
    nlinarith only [hmul]
  have hksqrt : 4 * Real.sqrt ((r : ℝ) * m) * Real.log m ≤ (k : ℝ) := by
    calc
      _ ≤ 4 * (2 * (N : ℝ) ^ ((a + b) / 2)) * ((b + 1) * Real.log N) := by
        apply mul_le_mul _ hlogm (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = (8 * (b + 1)) * (N : ℝ) ^ ((a + b) / 2) * Real.log N := by ring
      _ ≤ (N : ℝ) ^ v := hkN
      _ ≤ (k : ℝ) := hkvp.1
  have hsqrtmul : Real.sqrt ((r : ℝ) * m) * Real.sqrt ((r : ℝ) / m) = r := by
    rw [← Real.sqrt_mul (by positivity), show (r : ℝ) * m * ((r : ℝ) / m) = (r : ℝ)^2 by
      field_simp, Real.sqrt_sq (Nat.cast_nonneg r)]
  calc
    _ = (4 * Real.sqrt ((r : ℝ) * m) * Real.log m) * Real.sqrt ((r : ℝ) / m) := by
      calc
        _ = 4 * Real.log m * (Real.sqrt ((r : ℝ) * m) * Real.sqrt ((r : ℝ) / m)) := by
          rw [hsqrtmul]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hksqrt (Real.sqrt_nonneg _)

/-- Polynomial approximation uniform in `N`, including `b > 1`. -/
theorem polynomial_approximation {a b u : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : (a + b) / 2 < u) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℝ[X],
      (p.natDegree : ℝ) ≤ (N : ℝ) ^ u ∧ weight N p ≤ Real.exp ((N : ℝ) ^ u) ∧
      p.eval 0 = 1 ∧ ∀ x : ℕ, 1 ≤ x → x ≤ ⌈(N : ℝ) ^ b⌉₊ →
        |p.eval (x : ℝ)| ≤ Real.exp (-((N : ℝ) ^ a)) := by
  let g := (a + b) / 2
  let v := (g + u) / 2
  have hgu : g < u := hu
  have hag : a < g := by dsimp [g]; linarith
  have hgv : g < v := by dsimp [v]; linarith only [hgu]
  have hvu : v < u := by dsimp [v]; linarith only [hgu]
  have hav : a < v := lt_trans hag hgv
  have hb : 0 < b := lt_trans ha hab
  have hv : 0 < v := lt_trans ha hav
  have hexp : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) ^ b :=
    ((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 6, eventually_power_le hab 4,
    eventually_power_le hvu 4, eventually_power_log_le hvu 8,
    eventually_power_log_le hgv (8 * (b + 1)), hexp] with N hN habN hdegN hcostN hkN hexpN
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let r := ⌈(N : ℝ) ^ a⌉₊
  let m := ⌈(N : ℝ) ^ b⌉₊
  let k := ⌈(N : ℝ) ^ v⌉₊
  have hrap := ceil_rpow_bounds hN1 ha.le
  have hmbp := ceil_rpow_bounds hN1 hb.le
  have hkvp := ceil_rpow_bounds hN1 hv.le
  have hr1 : (1 : ℝ) ≤ r := (Real.one_le_rpow hN1R ha.le).trans hrap.1
  have hr : 1 ≤ r := by exact_mod_cast hr1
  have hm : 2 * r ≤ m := by
    have h : 2 * (r : ℝ) ≤ m := by nlinarith only [hrap.2, hmbp.1, habN]
    exact_mod_cast h
  have hlogm1 : 1 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hexpN.trans hmbp.1)
    simpa only [Real.log_exp] using h
  have hk := ceil_approx_condition (show 2 ≤ N by omega) ha.le hb.le hv.le hkN
  obtain ⟨hdeg, hweight, hzero, hdecay⟩ := approxPoly_bounds (Nat.cast_nonneg N) hr hm hk
  have havN : (N : ℝ) ^ a ≤ (N : ℝ) ^ v :=
    Real.rpow_le_rpow_of_exponent_le hN1R hav.le
  have hsum : (r : ℝ) + k ≤ 4 * (N : ℝ) ^ v := by
    nlinarith only [hrap.2, hkvp.2, havN]
  refine ⟨approxPoly r m k, ?_, ?_, hzero, ?_⟩
  · exact (by exact_mod_cast hdeg : ((approxPoly r m k).natDegree : ℝ) ≤ (r : ℝ) + k).trans
      (hsum.trans hdegN)
  · exact hweight.trans (approx_weight_exp hN hsum hcostN)
  · intro x hx0 hxm
    exact (hdecay x hx0 hxm).trans (approx_decay_exp hr hlogm1 hrap.1)


lemma eventually_two_powers_le {a b t : ℝ} (ha : a < t) (hb : b < t) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^a + (N:ℝ)^b ≤ (N:ℝ)^t := by
  filter_upwards [eventually_power_le ha 2,eventually_power_le hb 2] with N haN hbN
  linarith

/-- Every fixed coefficient and prefactor is absorbed by the strict power gaps. -/
lemma eventually_exp_power_gap {s u v : ℝ} (hs : s < v) (hu : u < v) (hv : 0 < v)
    (C ε D K : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * Real.exp (K*(N:ℝ)^u - (N:ℝ)^v) ≤
      ε * Real.exp (-(D*(N:ℝ)^s)) := by
  filter_upwards [eventually_power_le hv (3*Real.log (C/ε)),
    eventually_power_le hu (3*K),eventually_power_le hs (3*D)] with N h0 h1 h2
  simp only [Real.rpow_zero,mul_one] at h0
  calc
    _ = ε * Real.exp (Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v) := by
      rw [show Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v =
        Real.log (C/ε) + (K*(N:ℝ)^u - (N:ℝ)^v) by ring, Real.exp_add,
        Real.exp_log (div_pos hC hε)]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [h0,h1,h2])) hε.le

lemma ceil_power_log_bound {N : ℕ} {a : ℝ} (hN : 2 ≤ N) (ha : 0 ≤ a) :
    ((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1) ≤ 6*(N:ℝ)^a*Real.log N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N:ℝ)^a := Real.one_le_rpow hN1 ha
  have hc := (ceil_rpow_bounds (show 1 ≤ N by omega) ha).2
  have hl : Real.log (N+1) ≤ 2*Real.log N := by
    calc
      _ ≤ Real.log ((N:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith only [hN2])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog : 0 ≤ Real.log (N+1) := Real.log_nonneg (by linarith only [hN1])
  calc
    _ ≤ (3*(N:ℝ)^a)*Real.log (N+1) := mul_le_mul_of_nonneg_right (by linarith) hlog
    _ ≤ (3*(N:ℝ)^a)*(2*Real.log N) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by ring

lemma eventually_pattern_cost {a s v : ℝ} (ha : 0 ≤ a) (hav : a < v) (hsv : s < v) :
    ∀ᶠ N : ℕ in atTop,
      (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) * Real.exp (-((N:ℝ)^v)) ≤ Real.exp (-((N:ℝ)^s)) := by
  filter_upwards [eventually_power_log_le hav 12,eventually_power_le hsv 2,
    eventually_ge_atTop 2] with N hcost htarget hN
  have hc := ceil_power_log_bound hN ha
  have hp : (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) =
      Real.exp (((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1)) := by
    rw [show (⌈(N:ℝ)^a⌉₊:ℝ)+1 = ((⌈(N:ℝ)^a⌉₊+1:ℕ):ℝ) by push_cast; rfl,
      Real.exp_nat_mul,Real.exp_log (by positivity)]
  rw [hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hc,hcost,htarget]

lemma eventually_backward_cost {s a u w t : ℝ} (hs : 0 ≤ s) (hsa : s < a)
    (hau : a < u) (huw : u < w) (hwt : w < t) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) + Real.exp (-((N:ℝ)^a)) +
        (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤ Real.exp (-2*(N:ℝ)^s) := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hsu := hsa.trans hau
  have hsw := hsu.trans huw
  have hst := hsw.trans hwt
  filter_upwards [eventually_exp_power_gap hsw huw (ha.trans (hau.trans huw)) 1 (1/3) 2 1
      zero_lt_one (by norm_num),
    eventually_exp_power_gap hsa ha ha 1 (1/3) 2 0 zero_lt_one (by norm_num),
    eventually_exp_power_gap hst (huw.trans hwt) (lt_of_le_of_lt hs hst) 2 (1/3) 2 1
      (by norm_num) (by norm_num)] with N h1 h2 h3
  simp only [one_mul,zero_mul,zero_sub] at h1 h2 h3
  have hnon : 1 ≤ Real.exp ((N:ℝ)^u) := Real.one_le_exp (by positivity)
  have hlast : (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤
      2*Real.exp ((N:ℝ)^u-(N:ℝ)^t) := by
    rw [Real.exp_sub,div_eq_mul_inv,← Real.exp_neg]
    nlinarith only [hnon,Real.exp_pos (-((N:ℝ)^t))]
  have hlast' := hlast.trans h3
  have heq : -(2*(N:ℝ)^s) = -2*(N:ℝ)^s := by ring
  rw [heq] at h1 h2 hlast'
  linarith only [h1,h2,hlast']

end QAC

end

end OAI

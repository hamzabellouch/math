import OAI.Probability.FreeIsing.Estimates.EndpointTimeScale

namespace OAI

noncomputable section

namespace Problem367

theorem pathCutoff_applicability {C₀ C ω I : ℝ} {n : ℕ}
    (hCC : C₀ ≤ C) (hC : 0 ≤ C) (hω : 0 < ω) (hI : 1 ≤ I)
    (hn : pathCutoff C ω I ≤ n) : C₀ / ω ≤ (n : ℝ) := by
  calc
    C₀ / ω = C₀ * ω⁻¹ := div_eq_mul_inv _ _
    _ ≤ C * ω⁻¹ := mul_le_mul_of_nonneg_right hCC (by positivity)
    _ ≤ C * (ω⁻¹ + Real.log I) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith [Real.log_nonneg hI]
    _ ≤ (pathCutoff C ω I : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem tsum_endpoint_of_majorants {f g e : ℕ → ℝ} (R : ℕ)
    {P B E M : ℝ} (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (he0 : ∀ n, 0 ≤ e n) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hg : Summable g) (he : Summable e)
    (hprefix : (∑ n ∈ Finset.range R, f n) ≤ P)
    (htail : ∀ n, R ≤ n → f n ≤ B * g n + E * e n)
    (hM : (∑' n, g n) ≤ M) :
    (∑' n, f n) ≤ P + B * M + E * (∑' n, e n) := by
  have hmajorant := (hg.mul_left B).add (he.mul_left E)
  calc
    _ ≤ (∑ n ∈ Finset.range R, f n) + ∑' n, (B * g n + E * e n) :=
      tsum_le_prefix_add_majorant R hf0
        (fun n => add_nonneg (mul_nonneg hB (hg0 n)) (mul_nonneg hE (he0 n))) hmajorant htail
    _ = (∑ n ∈ Finset.range R, f n) +
        (B * (∑' n, g n) + E * (∑' n, e n)) := by
      rw [(hg.mul_left B).tsum_add (he.mul_left E), tsum_mul_left, tsum_mul_left]
    _ ≤ P + (B * M + E * (∑' n, e n)) :=
      add_le_add hprefix (add_le_add (mul_le_mul_of_nonneg_left hM hB) le_rfl)
    _ = _ := by ring

theorem tsum_scaled_integer_endpoint_le {f : ℕ → ℝ} (R k m : ℕ)
    {A B E c ω a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * (n : ℝ) ^ k)
    (htail : ∀ n, R ≤ n → f n ≤
      B * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * (R : ℝ) ^ (k + 1) +
      B * ((k.factorial : ℝ) * (2 / min c 1) ^ (k + 1) * (ω⁻¹) ^ (k + 1)) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  apply tsum_endpoint_of_majorants R hf0 (fun n => by positivity)
    (fun n => by positivity) hB hE (summable_path_attenuation k (mul_pos hc hω))
    (summable_superexponential_path m ha hq) _ htail
    (tsum_scaled_path_attenuation_le k hc hω hω1)
  calc
    _ ≤ ∑ n ∈ Finset.range R, A * (n : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      exact hshort n (Finset.mem_range.mp hn)
    _ = A * (∑ n ∈ Finset.range R, (n : ℝ) ^ k) := by rw [Finset.mul_sum]
    _ ≤ A * (R : ℝ) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (sum_range_nat_pow_le R k) hA

theorem tsum_scaled_sqrt_endpoint_le {f : ℕ → ℝ} (R m : ℕ)
    {A B E c ω a q : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤
      B * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * ((R : ℝ) * Real.sqrt R) +
      B * ((3 / (min c 1 * Real.sqrt (min c 1))) * (ω⁻¹ * Real.sqrt (ω⁻¹))) +
      E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-a * q ^ n)) := by
  apply tsum_endpoint_of_majorants R hf0 (fun n => by positivity)
    (fun n => by positivity) hB hE (summable_sqrt_path_attenuation (mul_pos hc hω))
    (summable_superexponential_path m ha hq) _ htail
    (tsum_scaled_sqrt_path_attenuation_le hc hω hω1)
  calc
    _ ≤ ∑ n ∈ Finset.range R, A * Real.sqrt n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hshort n (Finset.mem_range.mp hn)
    _ = A * (∑ n ∈ Finset.range R, Real.sqrt n) := by rw [Finset.mul_sum]
    _ ≤ A * ((R : ℝ) * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left (sum_range_sqrt_le R) hA

theorem tsum_cutoff_integer_endpoint_le {f : ℕ → ℝ} (R k m : ℕ)
    {A B E U V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * U * (n : ℝ) ^ k)
    (htail : ∀ n, R ≤ n → f n ≤
      B * U * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * U * (R : ℝ) ^ (k + 1) +
      (B * ((k.factorial : ℝ) * (2 / min c 1) ^ (k + 1))) * U * (ω⁻¹) ^ (k + 1) +
      (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) * V ^ 2 := by
  have htail' : ∀ n, R ≤ n → f n ≤
      (B * U) * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
      (E * V ^ 2) * ((n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n)) := by
    intro n hn
    have habs := pathCutoff_absorption hV hVK hK ha.le hq hC0 hC hbase hω hω1
      (show pathCutoff C ω (1 + Real.log (K / V)) ≤ n by simpa [← hR] using hn)
    calc
      f n ≤ _ := htail n hn
      _ ≤ B * U * ((n : ℝ) ^ k * Real.exp (-(c * ω) * n)) +
          E * ((n : ℝ) ^ m * (V ^ 2 * Real.exp (-(a / 2) * q ^ n))) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (by positivity)) hE
      _ = _ := by ring
  have hs := tsum_scaled_integer_endpoint_le R k m hf0
    (mul_nonneg hA hU) (mul_nonneg hB hU) (mul_nonneg hE (sq_nonneg V))
    hc hω hω1 (show 0 < a / 2 by positivity) hq hshort htail'
  convert hs using 1; ring

theorem pathCutoff_linear_absorption {V K a q C ω : ℝ} {n : ℕ}
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K) (ha : 0 ≤ a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ (a / 2) * q ^ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : pathCutoff C ω (1 + Real.log (K / V)) ≤ n) :
    Real.exp (-a * q ^ n) ≤ V * Real.exp (-(a / 2) * q ^ n) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlogratio : 0 ≤ Real.log (K / V) := Real.log_nonneg ((one_le_div hV).2 hVK)
  have hI : 1 ≤ 1 + Real.log (K / V) := by linarith
  have hexponent := path_log_cutoff_bound ha hq hI hC hbase
    (pathCutoff_log_bound hC0 hω hω1 hn)
  have hlog : -(a / 2) * q ^ n ≤ Real.log V := by
    rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hV)] at hexponent hlogratio
    linarith
  calc
    Real.exp (-a * q ^ n) = Real.exp (-(a / 2) * q ^ n) *
        Real.exp (-(a / 2) * q ^ n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log V) * Real.exp (-(a / 2) * q ^ n) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hlog) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_log hV]

theorem tsum_quadratic_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * S * n)
    (htail : ∀ n, R ≤ n → f n ≤ B * S *
      ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (2 * A * (C + 1) ^ 2 + B * (2 / min c 1) ^ 2)
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply quadratic_endpoint_scale hA (by positivity) hS (Nat.cast_nonneg R)
    (by positivity) (by positivity) (Real.log_nonneg hI) hscale
  have hs := tsum_cutoff_integer_endpoint_le R 1 m hf0 hA hB hE hS
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase hR
    (by simpa only [pow_one] using hshort) (by simpa only [pow_one] using htail)
  simpa using hs

theorem tsum_linear_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * V)
    (htail : ∀ n, R ≤ n → f n ≤ B * V * Real.exp (-(c * ω) * n) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (A * (C + 1) + B * (2 / min c 1))
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply linear_endpoint_scale hA (by positivity) hV.le (by positivity)
    (Real.log_nonneg hI) hscale
  have hs := tsum_cutoff_integer_endpoint_le R 0 m hf0 hA hB hE hV.le
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase hR
    (by simpa only [pow_zero, mul_one] using hshort)
    (by simpa only [pow_zero, one_mul] using htail)
  simpa using hs

theorem tsum_cutoff_sqrt_endpoint_le {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt S * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤ B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤ A * Real.sqrt S * ((R : ℝ) * Real.sqrt R) +
      (B * (3 / (min c 1 * Real.sqrt (min c 1)))) * Real.sqrt S *
        (ω⁻¹ * Real.sqrt (ω⁻¹)) +
      (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) * V := by
  have htail' : ∀ n, R ≤ n → f n ≤
      (B * Real.sqrt S) * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      (E * V) * ((n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n)) := by
    intro n hn
    have habs := pathCutoff_linear_absorption hV hVK hK ha.le hq hC0 hC hbase hω hω1
      (show pathCutoff C ω (1 + Real.log (K / V)) ≤ n by simpa [← hR] using hn)
    calc
      f n ≤ _ := htail n hn
      _ ≤ B * Real.sqrt S * (Real.sqrt n * Real.exp (-(c * ω) * n)) +
          E * ((n : ℝ) ^ m * (V * Real.exp (-(a / 2) * q ^ n))) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (by positivity)) hE
      _ = _ := by ring
  have hs := tsum_scaled_sqrt_endpoint_le R m hf0
    (mul_nonneg hA (Real.sqrt_nonneg S)) (mul_nonneg hB (Real.sqrt_nonneg S))
    (mul_nonneg hE hV.le) hc hω hω1 (show 0 < a / 2 by positivity) hq hshort htail'
  convert hs using 1; ring

theorem tsum_sqrt_endpoint_at_cutoff {f : ℕ → ℝ} (R m : ℕ)
    {A B E S V K c ω a q C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (ha : 0 < a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hR : R = pathCutoff C ω (1 + Real.log (K / V)))
    (hshort : ∀ n, n < R → f n ≤ A * Real.sqrt S * Real.sqrt n)
    (htail : ∀ n, R ≤ n → f n ≤ B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ m * Real.exp (-a * q ^ n))) :
    (∑' n, f n) ≤
      max (4 * A * (C + 1) * Real.sqrt (C + 1) +
        B * (3 / (min c 1 * Real.sqrt (min c 1))))
        (E * (∑' n : ℕ, (n : ℝ) ^ m * Real.exp (-(a / 2) * q ^ n))) *
      (Real.sqrt S * (ω⁻¹ * Real.sqrt (ω⁻¹) +
        Real.log (1 + Real.log (K / V)) * Real.sqrt (Real.log (1 + Real.log (K / V)))) + V) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hscale : (R : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log (1 + Real.log (K / V))) := by
    rw [hR]
    exact pathCutoff_le hC0 hω hω1 hI
  apply sqrt_endpoint_scale hA (by positivity) hV.le (Nat.cast_nonneg R)
    (by positivity) (by positivity) (Real.log_nonneg hI) hscale
  exact tsum_cutoff_sqrt_endpoint_le R m hf0 hA hB hE hV hVK hK
    hc hω hω1 ha hq hC0 hC hbase hR hshort htail

end Problem367

end

end OAI

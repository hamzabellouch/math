import Mathlib

namespace OAI

/-! Endpoint control for the even-degree correction in the circuit rank estimate. -/

namespace Problem335

open scoped BigOperators
open Set

/-- The logarithm of an exponential divided by its positive argument is convex. -/
theorem convexOn_affine_sub_log (A B : ℝ) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => A * x + B - Real.log x) := by
  have haff : ConvexOn ℝ (Ioi 0) (fun x : ℝ => A * x + B) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hB : (a + b) * B = B := by rw [hab, one_mul]
    nlinarith
  exact haff.sub strictConcaveOn_log_Ioi.concaveOn

/-- The quotient occurring in the even-degree error is bounded by its two
endpoint values. No smallness assumption on `q` is needed for this fact. -/
theorem rpow_affine_div_le_max_endpoints {q a b z c : ℝ}
    (hq : 0 < q) (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    q ^ (1 - c * z) / z ≤
      max (q ^ (1 - c * a) / a) (q ^ (1 - c * b) / b) := by
  have hz : 0 < z := ha.trans_le haz
  have hb : 0 < b := hz.trans_le hzb
  have hc := (convexOn_affine_sub_log (-c * Real.log q) (Real.log q)).le_max_of_mem_Icc
    ha hb ⟨haz, hzb⟩
  have hlog (x : ℝ) (hx : 0 < x) :
      Real.log (q ^ (1 - c * x) / x) =
        (-c * Real.log q) * x + Real.log q - Real.log x := by
    rw [Real.log_div (Real.rpow_pos_of_pos hq _).ne' hx.ne', Real.log_rpow hq]
    ring
  rw [← hlog z hz, ← hlog a ha, ← hlog b hb] at hc
  rcases le_max_iff.mp hc with hc | hc
  · exact le_max_of_le_left ((Real.log_le_log_iff (by positivity) (by positivity)).mp hc)
  · exact le_max_of_le_right ((Real.log_le_log_iff (by positivity) (by positivity)).mp hc)

/-- Summing the endpoint estimate charges each term by its degree, rather
than by the number of factors. This avoids a constant loss per even degree. -/
theorem sum_rpow_affine_le_endpoint_mul_sum {ι : Type*} (s : Finset ι)
    (d : ι → ℝ) {q a b c : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hd : ∀ i ∈ s, a ≤ d i ∧ d i ≤ b) :
    (∑ i ∈ s, q ^ (1 - c * d i)) ≤
      max (q ^ (1 - c * a) / a) (q ^ (1 - c * b) / b) * ∑ i ∈ s, d i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hdi : 0 < d i := ha.trans_le (hd i hi).1
  exact (div_le_iff₀ hdi).mp
    (rpow_affine_div_le_max_endpoints hq ha (hd i hi).1 (hd i hi).2)

/-- A total degree bound turns the preceding weighted estimate into a bound
independent of the number of terms. -/
theorem sum_rpow_affine_le_endpoint_mul {ι : Type*} (s : Finset ι)
    (d : ι → ℝ) {q a b c N : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hd : ∀ i ∈ s, a ≤ d i ∧ d i ≤ b) (hs : (∑ i ∈ s, d i) ≤ N) :
    (∑ i ∈ s, q ^ (1 - c * d i)) ≤
      max (q ^ (1 - c * a) / a) (q ^ (1 - c * b) / b) * N := by
  apply (sum_rpow_affine_le_endpoint_mul_sum s d hq ha hd).trans
  apply mul_le_mul_of_nonneg_left hs
  exact le_trans (by positivity : 0 ≤ q ^ (1 - c * a) / a) (le_max_left _ _)

/-- The exact square-root error bound needed after estimating the two endpoint
quotients by `C / sqrt N`. -/
theorem sum_rpow_affine_le_mul_sqrt {ι : Type*} (s : Finset ι)
    (d : ι → ℝ) {q a b c N C : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hN : 0 < N) (hd : ∀ i ∈ s, a ≤ d i ∧ d i ≤ b)
    (hs : (∑ i ∈ s, d i) ≤ N)
    (hleft : q ^ (1 - c * a) / a ≤ C / Real.sqrt N)
    (hright : q ^ (1 - c * b) / b ≤ C / Real.sqrt N) :
    (∑ i ∈ s, q ^ (1 - c * d i)) ≤ C * Real.sqrt N := by
  calc
    _ ≤ max (q ^ (1 - c * a) / a) (q ^ (1 - c * b) / b) * N :=
      sum_rpow_affine_le_endpoint_mul s d hq ha hd hs
    _ ≤ (C / Real.sqrt N) * N :=
      mul_le_mul_of_nonneg_right (max_le hleft hright) hN.le
    _ = C * Real.sqrt N := by
      have hsq := Real.sq_sqrt hN.le
      have hne : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      field_simp
      rw [hsq]

/-- The left endpoint correction is uniformly bounded. -/
theorem evenCorrection_left_endpoint {N s q : ℝ} (hN : 0 < N)
    (hs : 0 ≤ s) (hsN : s ≤ Real.sqrt N)
    (hqlo : (Real.sqrt N)⁻¹ ≤ q) (hqhi : q ≤ 2 / Real.sqrt N) :
    q ^ (1 - (s / N) * 2) / 2 ≤ Real.exp 2 / Real.sqrt N := by
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hq : 0 < q := (inv_pos.mpr hroot).trans_le hqlo
  have hlogq : -Real.log q ≤ Real.sqrt N := by
    have hlog := Real.log_le_log (inv_pos.mpr hroot) hqlo
    rw [Real.log_inv] at hlog
    have hrootlog := Real.log_le_sub_one_of_pos hroot
    linarith
  have hc : 0 ≤ 2 * s / N := by positivity
  have hrootbound : (2 * s / N) * Real.sqrt N ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN]
    have hsq := Real.sq_sqrt hN.le
    have hmul := mul_le_mul_of_nonneg_right hsN hroot.le
    nlinarith
  have hexponent : (-(s / N * 2)) * Real.log q ≤ 2 := by
    calc
      _ = (2 * s / N) * (-Real.log q) := by ring
      _ ≤ (2 * s / N) * Real.sqrt N := mul_le_mul_of_nonneg_left hlogq hc
      _ ≤ 2 := hrootbound
  have hpower : q ^ (-(s / N * 2)) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos hq]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hexponent)
  rw [sub_eq_add_neg, Real.rpow_add hq, Real.rpow_one]
  have hp := mul_le_mul hqhi hpower (Real.rpow_nonneg hq.le _) (by positivity)
  calc
    q * q ^ (-(s / N * 2)) / 2 ≤ ((2 / Real.sqrt N) * Real.exp 2) / 2 := by linarith
    _ = Real.exp 2 / Real.sqrt N := by ring

/-- The right endpoint correction needs only `q ≤ 1`. -/
theorem evenCorrection_right_endpoint {N s q : ℝ} (hN : 0 < N)
    (hs : 0 < s) (hsN : s ≤ Real.sqrt N) (hq : 0 ≤ q) (hqone : q ≤ 1) :
    q ^ (1 - (s / N) * (N / (4 * s))) / (N / (4 * s)) ≤
      4 / Real.sqrt N := by
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have ht : 0 < N / (4 * s) := by positivity
  have he : 1 - (s / N) * (N / (4 * s)) = (3 / 4 : ℝ) := by
    field_simp
    ring
  rw [he]
  have hp : q ^ (3 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hq hqone (by norm_num)
  apply (div_le_div_of_nonneg_right hp ht.le).trans
  rw [div_le_div_iff₀ ht hroot]
  have heq : N / (4 * s) * (4 * s) = N := div_mul_cancel₀ _ (by positivity)
  have hsq := Real.sq_sqrt hN.le
  have hmul := mul_le_mul_of_nonneg_left hsN hroot.le
  nlinarith

/-- An explicit uniform square-root bound for the sum of all low-even-degree
corrections. Only the numerical range of degrees is needed, not their parity. -/
theorem evenCorrection_sum_bound {ι : Type*} (I : Finset ι) (d : ι → ℝ)
    {N s q : ℝ} (hN : 0 < N) (hs : 0 < s) (hsN : s ≤ Real.sqrt N)
    (hqlo : (Real.sqrt N)⁻¹ ≤ q) (hqhi : q ≤ 2 / Real.sqrt N) (hqone : q ≤ 1)
    (hd : ∀ i ∈ I, 2 ≤ d i ∧ d i ≤ N / (4 * s))
    (hdsum : (∑ i ∈ I, d i) ≤ N) :
    (∑ i ∈ I, q ^ (1 - (s / N) * d i)) ≤
      (Real.exp 2 + 4) * Real.sqrt N := by
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hq : 0 < q := (inv_pos.mpr hroot).trans_le hqlo
  apply sum_rpow_affine_le_mul_sqrt I d hq (by norm_num) hN hd hdsum
  · apply (evenCorrection_left_endpoint hN hs.le hsN hqlo hqhi).trans
    apply div_le_div_of_nonneg_right _ hroot.le
    linarith
  · apply (evenCorrection_right_endpoint hN hs hsN hq.le hqone).trans
    apply div_le_div_of_nonneg_right _ hroot.le
    linarith [Real.exp_pos (2 : ℝ)]

/-- The correction bound specialized to the low even members of a list of
positive integer degrees with bounded total degree. -/
theorem sum_low_even_corrections {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {N s q : ℝ} (hN : 0 < N) (hs : 0 < s) (hsN : s ≤ Real.sqrt N)
    (hqlo : (Real.sqrt N)⁻¹ ≤ q) (hqhi : q ≤ 2 / Real.sqrt N) (hqone : q ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (hsum : (∑ i ∈ I, (e i : ℝ)) ≤ N) :
    (∑ i ∈ I, if Even (e i) ∧ (e i : ℝ) < N / (4 * s)
      then 4 * q ^ (1 - (s / N) * e i) else 0) ≤
      (4 * (Real.exp 2 + 4)) * Real.sqrt N := by
  classical
  let J := I.filter (fun i => Even (e i) ∧ (e i : ℝ) < N / (4 * s))
  have hd : ∀ i ∈ J, 2 ≤ (e i : ℝ) ∧ (e i : ℝ) ≤ N / (4 * s) := by
    intro i hi
    obtain ⟨hiI, hiEven, hiBound⟩ := Finset.mem_filter.mp hi
    refine ⟨?_, hiBound.le⟩
    have hpos := he i hiI
    obtain ⟨k, hk⟩ := hiEven
    have htwo : 2 ≤ e i := by omega
    exact_mod_cast htwo
  have hsumJ : (∑ i ∈ J, (e i : ℝ)) ≤ N := by
    apply le_trans _ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi hin
    positivity
  have h := evenCorrection_sum_bound J (fun i => (e i : ℝ)) hN hs hsN
    hqlo hqhi hqone hd hsumJ
  calc
    _ = 4 * ∑ i ∈ J, q ^ (1 - (s / N) * e i) := by
      rw [Finset.mul_sum]
      simp only [J, Finset.sum_filter]
    _ ≤ 4 * ((Real.exp 2 + 4) * Real.sqrt N) := by linarith
    _ = _ := by ring

end Problem335

end OAI

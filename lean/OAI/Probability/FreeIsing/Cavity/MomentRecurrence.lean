import OAI.Probability.FreeIsing.Energy.MixedMoments
import OAI.Probability.FreeIsing.Energy.MomentTail

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem critical_cavity_moment_step
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK : 0 ≤ K) (ht : 0 < t)
    (hlog : Real.log ((b : ℝ) + 1) ≤ 2 * K)
    (hsmall : Real.exp (-9 * K / 2) + ((b : ℝ) + 1)^3 * Real.exp (-4 * K) ≤ 1 - theta)
    (A : ℕ → ℝ) {p : ℕ} (hp : 3 ≤ p)
    {X : Fin (b + 1) → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i))
    (hMom : ∀ i (k : ℕ), k ≤ p → Integrable (fun ω => |X i ω|^k) μ)
    (hRec : A p ≤ ∫ ω, |∑ i, X i ω|^p ∂μ)
    (hOwn : ∀ k : ℕ, k ≤ p → (∫ ω, |X 0 ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ (i : Fin b) k, k ≤ p → (∫ ω, |X i.succ ω|^k ∂μ) ≤ theta^k * A k)
    (hLower : ∀ k, k < p → A k ≤ Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  have hbound : ∀ (i : Fin (b + 1)) k, k < p → (∫ ω, |X i ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4) := by
    intro i k hk
    refine Fin.cases ?_ (fun j => ?_) i
    · calc
        _ ≤ Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4) := hOwn k hk.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hK (sq_nonneg (k : ℝ))]))
          (Real.rpow_nonneg ht.le _)
    · calc
        _ ≤ theta^k * A k := hChild j k hk.le
        _ ≤ theta^k * (Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hLower k hk) (pow_nonneg htheta _)
        _ ≤ _ := mul_le_of_le_one_left (by positivity) (pow_le_one₀ htheta htheta1.le)
  have hest := independent_abs_moment_le_pure_add_remainder hX hmX
    (show 0 < p by omega) hMom hK ht hbound
  have hpure : (∑ i : Fin (b + 1), ∫ ω, |X i ω|^p ∂μ) ≤
      Real.exp (K * (p : ℝ)^2 / 2) * t ^ ((p : ℝ) / 4) +
        (b : ℝ) * theta^p * A p := by
    rw [Fin.sum_univ_succ]
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) => hChild i p (le_refl _))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    have := add_le_add (hOwn p (le_refl _)) hh
    simpa only [mul_assoc] using this
  have hrec' : (1 - (b : ℝ) * theta^p) * A p ≤
      (Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) *
      (Real.exp (-K * (p : ℝ)^2 / 2) +
        ((b : ℝ) + 1)^p * Real.exp (-2 * K * ((p : ℝ) - 1))) := by
    have hh := hRec.trans (hest.trans (add_le_add hpure (le_refl _)))
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hh
    have he1 : Real.exp (K * (p : ℝ)^2 / 2) =
        Real.exp (K * (p : ℝ)^2) * Real.exp (-K * (p : ℝ)^2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) =
        Real.exp (K * (p : ℝ)^2) * Real.exp (-2 * K * ((p : ℝ) - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he1, he2] at hh
    nlinarith
  apply critical_moment_absorb (Nat.cast_nonneg b) htheta htheta1 hcritical hp
    (by positivity) (e := Real.exp (-K * (p : ℝ)^2 / 2) +
      ((b : ℝ) + 1)^p * Real.exp (-2 * K * ((p : ℝ) - 1))) _ hrec'
  exact (critical_moment_error_le_order_three (by positivity) hK hlog hp).trans hsmall

theorem critical_all_moments_of_independent_recursion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK : 0 ≤ K) (ht : 0 < t)
    (hlog : Real.log ((b : ℝ) + 1) ≤ 2 * K)
    (hsmall : Real.exp (-9 * K / 2) + ((b : ℝ) + 1)^3 * Real.exp (-4 * K) ≤ 1 - theta)
    (A : ℕ → ℝ) {X : Fin (b + 1) → Ω → ℝ}
    (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    (hMom : ∀ i (k : ℕ), Integrable (fun ω => |X i ω|^k) μ)
    (hRec : ∀ p, A p ≤ ∫ ω, |∑ i, X i ω|^p ∂μ)
    (hOwn : ∀ k : ℕ, (∫ ω, |X 0 ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ (i : Fin b) k, (∫ ω, |X i.succ ω|^k ∂μ) ≤ theta^k * A k)
    (hbase : ∀ p, p < 3 → A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∀ p, A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp : p < 3
    · exact hbase p hp
    · exact critical_cavity_moment_step htheta htheta1 hcritical hK ht hlog hsmall A
        (by omega) hX hmX (fun i k _ => hMom i k) (hRec p)
        (fun k _ => hOwn k) (fun i k _ => hChild i k) ih

theorem exists_critical_all_moments_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K0 t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK0 : 0 ≤ K0) (ht : 0 < t)
    (A : ℕ → ℝ) {X : Fin (b + 1) → Ω → ℝ}
    (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    (hMom : ∀ i (k : ℕ), Integrable (fun ω => |X i ω|^k) μ)
    (hRec : ∀ p, A p ≤ ∫ ω, |∑ i, X i ω|^p ∂μ)
    (hOwn : ∀ k : ℕ, (∫ ω, |X 0 ω|^k ∂μ) ≤
      Real.exp (K0 * (k : ℝ)^2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ (i : Fin b) k, (∫ ω, |X i.succ ω|^k ∂μ) ≤ theta^k * A k)
    (hbase : ∀ p, p < 3 → A p ≤ Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 ≤ K ∧
      ∀ p, A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  obtain ⟨K, hKK0, hK, hlog, hsmall⟩ :=
    exists_critical_moment_constant (m := (b : ℝ) + 1) (by positivity)
      (show 0 < 1 - theta by linarith) (2 * K0)
  have hKK0' : K0 ≤ K := by linarith
  refine ⟨K, hKK0', hK, ?_⟩
  apply critical_all_moments_of_independent_recursion htheta htheta1 hcritical hK ht hlog hsmall A
    hX hmX hMom hRec ?_ hChild ?_
  · intro k
    apply (hOwn k).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hKK0) (sq_nonneg (k : ℝ))]
  · intro p hp
    apply (hbase p hp).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKK0' (sq_nonneg _))

theorem exists_uniform_critical_all_moments_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK0 : 0 ≤ K0)
    (S : Set ℝ) (ht : ∀ t ∈ S, 0 < t)
    (A : ℝ → ℕ → ℝ) (X : ℝ → Fin (b + 1) → Ω → ℝ)
    (hX : ∀ t ∈ S, iIndepFun (X t) μ)
    (hmX : ∀ t ∈ S, ∀ i, Measurable (X t i))
    (hMom : ∀ t ∈ S, ∀ i (k : ℕ), Integrable (fun ω => |X t i ω|^k) μ)
    (hRec : ∀ t ∈ S, ∀ p, A t p ≤ ∫ ω, |∑ i, X t i ω|^p ∂μ)
    (hOwn : ∀ t ∈ S, ∀ k : ℕ, (∫ ω, |X t 0 ω|^k ∂μ) ≤
      Real.exp (K0 * (k : ℝ)^2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ t ∈ S, ∀ (i : Fin b) k,
      (∫ ω, |X t i.succ ω|^k ∂μ) ≤ theta^k * A t k)
    (hbase : ∀ t ∈ S, ∀ p, p < 3 →
      A t p ≤ Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 ≤ K ∧
      ∀ t ∈ S, ∀ p, A t p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  obtain ⟨K, hKK0, hK, hlog, hsmall⟩ :=
    exists_critical_moment_constant (m := (b : ℝ) + 1) (by positivity)
      (show 0 < 1 - theta by linarith) (2 * K0)
  have hKK0' : K0 ≤ K := by linarith
  refine ⟨K, hKK0', hK, ?_⟩
  intro t htS
  apply critical_all_moments_of_independent_recursion htheta htheta1 hcritical hK
    (ht t htS) hlog hsmall (A t) (hX t htS) (hmX t htS) (hMom t htS) (hRec t htS)
    ?_ (hChild t htS) ?_
  · intro k
    apply (hOwn t htS k).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (ht t htS).le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hKK0) (sq_nonneg (k : ℝ))]
  · intro p hp
    apply (hbase t htS p hp).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (ht t htS).le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKK0' (sq_nonneg _))

theorem exists_uniform_critical_moment_and_tail_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK0 : 0 < K0)
    (S : Set ℝ) (ht : ∀ t ∈ S, 0 < t)
    (Y : ℝ → Ω → ℝ) (X : ℝ → Fin (b + 1) → Ξ → ℝ)
    (hY : ∀ t ∈ S, ∀ p : ℕ, Integrable (fun ω => |Y t ω|^p) μ)
    (hX : ∀ t ∈ S, iIndepFun (X t) ν)
    (hmX : ∀ t ∈ S, ∀ i, Measurable (X t i))
    (hMom : ∀ t ∈ S, ∀ i (k : ℕ), Integrable (fun ω => |X t i ω|^k) ν)
    (hRec : ∀ t ∈ S, ∀ p : ℕ,
      (∫ ω, |Y t ω|^p ∂μ) ≤ ∫ ω, |∑ i, X t i ω|^p ∂ν)
    (hOwn : ∀ t ∈ S, ∀ k : ℕ, (∫ ω, |X t 0 ω|^k ∂ν) ≤
      Real.exp (K0 * (k : ℝ)^2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ t ∈ S, ∀ (i : Fin b) (k : ℕ),
      (∫ ω, |X t i.succ ω|^k ∂ν) ≤ theta^k * ∫ ω, |Y t ω|^k ∂μ)
    (hbase : ∀ t ∈ S, ∀ p : ℕ, p < 3 →
      (∫ ω, |Y t ω|^p ∂μ) ≤ Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 < K ∧
      (∀ t ∈ S, ∀ p : ℕ, (∫ ω, |Y t ω|^p ∂μ) ≤
        Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) ∧
      (∀ t ∈ S, 32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y t ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t)^2) / (512 * K)))) := by
  obtain ⟨K, hKK0, _, hbound⟩ :=
    exists_uniform_critical_all_moments_bound htheta htheta1 hcritical hK0.le S ht
      (fun t p => ∫ ω, |Y t ω|^p ∂μ) X hX hmX hMom hRec hOwn hChild hbase
  have hK : 0 < K := hK0.trans_le hKK0
  refine ⟨K, hKK0, hK, hbound, ?_⟩
  intro t htS hsmall
  exact measure_abs_gt_rpow_le_of_moments hK (ht t htS) hsmall
    (fun p _ => hY t htS p) (fun p _ => hbound t htS p)

theorem exists_small_time_for_moment_tail {K t0 : ℝ} (ht0 : 0 < t0) :
    ∃ tTail : ℝ, 0 < tTail ∧ tTail ≤ t0 ∧
      ∀ t : ℝ, 0 < t → t ≤ tTail → 32 * K ≤ Real.log (1 / t) := by
  refine ⟨min t0 (Real.exp (-32 * K)), lt_min ht0 (Real.exp_pos _), min_le_left _ _, ?_⟩
  intro t ht htt
  have hte : t ≤ Real.exp (-32 * K) := htt.trans (min_le_right _ _)
  have hl := Real.log_le_log ht hte
  rw [Real.log_exp] at hl
  rw [one_div, Real.log_inv]
  linarith

end Problem367

end OAI

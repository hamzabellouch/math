import OAI.Probability.FreeIsing.Cavity.BaseMoments
import OAI.Probability.FreeIsing.Cavity.MomentRecurrence
import OAI.Probability.FreeIsing.Cavity.MomentTransport
import OAI.Probability.FreeIsing.Energy.MomentTail
import OAI.Probability.FreeIsing.Gaussian.Moments

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem exists_uniform_critical_gaussian_recursion_tail
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta ^ 2 = 1) (hK0 : 2 ≤ K0) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 < K ∧
      ∀ (t : ℝ), 0 < t → t ≤ 1 →
      ∀ (Y : Ω → ℝ) (G : Ξ → ℝ) (X : Fin (b + 1) → Ξ → ℝ),
      HasLaw G (gaussianReal 0 1) ν →
      (X 0 =ᵐ[ν] fun ω => t + Real.sqrt t * G ω) →
      iIndepFun X ν → (∀ i, Measurable (X i)) →
      (∀ (i : Fin b) p, Integrable (fun ω => |X i.succ ω| ^ p) ν) →
      (∀ p : ℕ, Integrable (fun ω => |Y ω| ^ p) μ) →
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤ ∫ ω, |∑ i, X i ω| ^ p ∂ν) →
      (∀ (i : Fin b) p, (∫ ω, |X i.succ ω| ^ p ∂ν) ≤
        theta ^ p * ∫ ω, |Y ω| ^ p ∂μ) →
      (∀ p : ℕ, p < 3 → (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K0 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) →
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)))) := by
  obtain ⟨K, hKK0, hK, hlog, hsmall⟩ :=
    exists_critical_moment_constant (m := (b : ℝ) + 1) (by positivity)
      (show 0 < 1 - theta by linarith) (2 * K0)
  have hKpos : 0 < K := by linarith
  have hK0K : K0 ≤ K := by linarith
  refine ⟨K, hK0K, hKpos, ?_⟩
  intro t ht ht1 Y G X hG hOwn hX hmX hChildInt hYInt hRec hChild hbase
  have hOwnPow (p : ℕ) :
      (fun ω => |X 0 ω| ^ p) =ᵐ[ν] fun ω => |t + Real.sqrt t * G ω| ^ p :=
    hOwn.fun_comp (fun x : ℝ => |x| ^ p)
  have hMom : ∀ i (p : ℕ), Integrable (fun ω => |X i ω| ^ p) ν := by
    intro i p
    refine Fin.cases ?_ (fun j => hChildInt j p) i
    exact (integrable_gaussian_observation_abs_pow_of_hasLaw hG ht.le ht1 p).congr
      (hOwnPow p).symm
  have hOwnBound (p : ℕ) : (∫ ω, |X 0 ω| ^ p ∂ν) ≤
      Real.exp (K * (p : ℝ) ^ 2 / 2) * t ^ ((p : ℝ) / 4) := by
    rw [integral_congr_ae (hOwnPow p)]
    by_cases hp : p = 0
    · subst p
      simp
    have hbound := integral_gaussian_observation_abs_pow_le_of_hasLaw hG ht ht1
      (show 1 ≤ p by omega)
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (p : ℝ),
      mul_nonneg (show 0 ≤ K - 4 by linarith) (sq_nonneg (p : ℝ))]
  have hmom : ∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
      Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
    apply critical_all_moments_of_independent_recursion htheta htheta1 hcritical hK ht
      hlog hsmall (fun p => ∫ ω, |Y ω| ^ p ∂μ) hX hmX hMom hRec hOwnBound hChild
    intro p hp
    apply (hbase p hp).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK0K (sq_nonneg _))
  refine ⟨hmom, fun htime => ?_⟩
  exact measure_abs_gt_rpow_le_of_moments hKpos ht htime
    (fun p _ => hYInt p) (fun p _ => hmom p)

theorem cavity_base_moments_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G Y : Ω → ℝ} {B C t : ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) (hY : AEMeasurable Y μ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * G ω)| ≤ B)
    (hinfo : (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) ≤ C * Real.sqrt t) :
    ∀ p : ℕ, p < 3 → (∫ ω, |Y ω| ^ p ∂μ) ≤
      Real.exp ((2 + cavityBaseConstant B C + Real.sqrt (cavityBaseConstant B C)) *
        (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
  have hD : 0 < cavityBaseConstant B C := cavityBaseConstant_pos hC
  have hS := Real.sqrt_nonneg (cavityBaseConstant B C)
  intro p hp
  interval_cases p
  · simp
  · have hfirst := cavity_base_first_moment hG hY hB hC ht ht1 hbound hinfo
    norm_num only [Nat.cast_one, one_pow, pow_one, mul_one] at *
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    have hexp := Real.add_one_le_exp
      (2 + cavityBaseConstant B C + Real.sqrt (cavityBaseConstant B C))
    linarith
  · have hsecond := (cavity_base_second_moment hG hY hB ht ht1 hbound hinfo).2
    simp only [sq_abs] at ⊢
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, div_self] at ⊢
    have hpow : t ^ (1 / 2 : ℝ) = Real.sqrt t := by
      exact (Real.sqrt_eq_rpow t).symm
    rw [hpow]
    apply hsecond.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg t)
    have hexp := Real.add_one_le_exp
      ((2 + cavityBaseConstant B C + Real.sqrt (cavityBaseConstant B C)) * (2 : ℝ)^2)
    norm_num only [show (2 : ℝ)^2 = 4 by norm_num] at hexp
    nlinarith

theorem exists_uniform_critical_information_recursion_tail
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta B C : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta ^ 2 = 1) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (t : ℝ), 0 < t → t ≤ 1 →
      ∀ (Y GY : Ω → ℝ) (G : Ξ → ℝ) (X : Fin (b + 1) → Ξ → ℝ),
      AEMeasurable Y μ → HasLaw GY (gaussianReal 0 1) μ →
      (∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * GY ω)| ≤ B) →
      ((∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) ≤ C * Real.sqrt t) →
      HasLaw G (gaussianReal 0 1) ν →
      (X 0 =ᵐ[ν] fun ω => t + Real.sqrt t * G ω) →
      iIndepFun X ν → (∀ i, Measurable (X i)) →
      (∀ (i : Fin b) p, Integrable (fun ω => |X i.succ ω| ^ p) ν) →
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤ ∫ ω, |∑ i, X i ω| ^ p ∂ν) →
      (∀ (i : Fin b) p, (∫ ω, |X i.succ ω| ^ p ∂ν) ≤
        theta ^ p * ∫ ω, |Y ω| ^ p ∂μ) →
      (∀ p : ℕ, Integrable (fun ω => |Y ω| ^ p) μ) ∧
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)))) := by
  let K0 : ℝ := 2 + cavityBaseConstant B C + Real.sqrt (cavityBaseConstant B C)
  have hK0 : 2 ≤ K0 := by
    dsimp [K0]
    linarith [cavityBaseConstant_pos (B := B) hC,
      Real.sqrt_nonneg (cavityBaseConstant B C)]
  obtain ⟨K, _, hK, htail⟩ := exists_uniform_critical_gaussian_recursion_tail
    (μ := μ) (ν := ν) htheta htheta1 hcritical hK0
  refine ⟨K, hK, ?_⟩
  intro t ht ht1 Y GY G X hY hGY hbound hinfo hG hOwn hX hmX hChildInt hRec hChild
  have hYInt := integrable_cavity_abs_pow_of_gaussian_bound hGY hY hB ht.le ht1 hbound
  refine ⟨hYInt, ?_⟩
  apply htail t ht ht1 Y G X hG hOwn hX hmX hChildInt hYInt hRec hChild
  exact cavity_base_moments_exp_bound hGY hY hB hC ht ht1 hbound hinfo

theorem exists_uniform_critical_information_response_tail
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta B C : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta ^ 2 = 1) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (t : ℝ), 0 < t → t ≤ 1 →
      ∀ (Y GY : Ω → ℝ) (Ycond G : Ξ → ℝ)
        (Z : Fin (b + 1) → Ξ → ℝ) (psi : ℝ → ℝ),
      AEMeasurable Y μ → HasLaw GY (gaussianReal 0 1) μ →
      (∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * GY ω)| ≤ B) →
      ((∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) ≤ C * Real.sqrt t) →
      HasLaw G (gaussianReal 0 1) ν →
      (Z 0 =ᵐ[ν] fun ω => t + Real.sqrt t * G ω) →
      iIndepFun Z ν → (∀ i, Measurable (Z i)) →
      Measurable psi → (∀ z, |psi z| ≤ theta * |z|) →
      IdentDistrib (fun ω => |Ycond ω|) (fun ω => |Y ω|) ν μ →
      (∀ i : Fin b, IdentDistrib (fun ω => |Z i.succ ω|) (fun ω => |Y ω|) ν μ) →
      (∀ᵐ ω ∂ν, Ycond ω =
        ∑ i : Fin (b + 1), Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i) →
      (∀ p : ℕ, Integrable (fun ω => |Y ω| ^ p) μ) ∧
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)))) := by
  obtain ⟨K, hK, htail⟩ := exists_uniform_critical_information_recursion_tail
    (μ := μ) (ν := ν) htheta htheta1 hcritical hB hC
  refine ⟨K, hK, ?_⟩
  intro t ht ht1 Y GY Ycond G Z psi hY hGY hbound hinfo hG hOwn hZ hmZ
    hpsi hcontract hCond hChild hEq
  let X : Fin (b + 1) → Ξ → ℝ :=
    fun i ω => Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i
  have hYInt := integrable_cavity_abs_pow_of_gaussian_bound hGY hY hB ht.le ht1 hbound
  have hXi : iIndepFun X ν := iIndepFun_cavity_response hZ hpsi
  have hmX : ∀ i, Measurable (X i) := by
    intro i
    exact Fin.cases (hmZ 0) (fun j => hpsi.comp (hmZ j.succ)) i
  have hChildMoment (i : Fin b) (p : ℕ) :=
    response_abs_moment_of_identDistrib_abs (hChild i) hpsi (hmZ i.succ)
      hcontract p (hYInt p)
  have hRec : ∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤ ∫ ω, |∑ i, X i ω| ^ p ∂ν := by
    intro p
    apply le_of_eq
    calc
      _ = ∫ ω, |Ycond ω| ^ p ∂ν := (abs_moment_of_identDistrib_abs hCond p).2.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hEq] with ω hω
        exact congrArg (fun x : ℝ => |x| ^ p) hω)
  exact htail t ht ht1 Y GY G X hY hGY hbound hinfo hG hOwn hXi hmX
    (fun i p => (hChildMoment i p).1) hRec (fun i p => (hChildMoment i p).2)

end Problem367

end OAI

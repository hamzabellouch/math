import OAI.Probability.FreeIsing.Cavity.MomentTransport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem exists_measure_uniform_critical_response_moment_and_tail_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta ^ 2 = 1) (hK0 : 0 < K0) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 < K ∧
      ∀ (μ : Measure Ω) (ν : Measure Ξ),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      ∀ (t : ℝ), 0 < t →
      ∀ (Y : Ω → ℝ) (Ycond : Ξ → ℝ) (Z : Fin (b + 1) → Ξ → ℝ)
        (psi : ℝ → ℝ),
      Measurable psi → (∀ z, |psi z| ≤ theta * |z|) →
      (∀ p : ℕ, Integrable (fun ω => |Y ω| ^ p) μ) →
      (∀ p : ℕ, Integrable (fun ω => |Z 0 ω| ^ p) ν) →
      iIndepFun Z ν → (∀ i, Measurable (Z i)) →
      IdentDistrib (fun ω => |Ycond ω|) (fun ω => |Y ω|) ν μ →
      (∀ i : Fin b, IdentDistrib (fun ω => |Z i.succ ω|)
        (fun ω => |Y ω|) ν μ) →
      (∀ᵐ ω ∂ν, Ycond ω =
        ∑ i : Fin (b + 1), Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i) →
      (∀ p : ℕ, (∫ ω, |Z 0 ω| ^ p ∂ν) ≤
        Real.exp (K0 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) →
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
  have hK0K : K0 ≤ K := by linarith
  have hKpos : 0 < K := hK0.trans_le hK0K
  refine ⟨K, hK0K, hKpos, ?_⟩
  intro μ ν hμ hν t ht Y Ycond Z psi hpsi hcontract hY hOwnInt hZ hmZ
    hCond hChild hEq hOwn hbase
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let X : Fin (b + 1) → Ξ → ℝ :=
    fun i ω => Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i
  have hXi : iIndepFun X ν := iIndepFun_cavity_response hZ hpsi
  have hmX : ∀ i, Measurable (X i) := by
    intro i
    exact Fin.cases (hmZ 0) (fun j => hpsi.comp (hmZ j.succ)) i
  have hChildMoment (i : Fin b) (p : ℕ) :=
    response_abs_moment_of_identDistrib_abs (hChild i) hpsi (hmZ i.succ)
      hcontract p (hY p)
  have hMom : ∀ i (p : ℕ), Integrable (fun ω => |X i ω| ^ p) ν := by
    intro i p
    exact Fin.cases (hOwnInt p) (fun j => (hChildMoment j p).1) i
  have hRec (p : ℕ) : (∫ ω, |Y ω| ^ p ∂μ) ≤ ∫ ω, |∑ i, X i ω| ^ p ∂ν := by
    apply le_of_eq
    calc
      _ = ∫ ω, |Ycond ω| ^ p ∂ν := (abs_moment_of_identDistrib_abs hCond p).2.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hEq] with ω hω
        exact congrArg (fun x : ℝ => |x| ^ p) hω)
  have hOwnBound (p : ℕ) : (∫ ω, |X 0 ω| ^ p ∂ν) ≤
      Real.exp (K * (p : ℝ) ^ 2 / 2) * t ^ ((p : ℝ) / 4) := by
    apply (hOwn p).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hKK0) (sq_nonneg (p : ℝ))]
  have hmom : ∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
      Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
    apply critical_all_moments_of_independent_recursion htheta htheta1 hcritical hK ht
      hlog hsmall (fun p => ∫ ω, |Y ω| ^ p ∂μ) hXi hmX hMom hRec hOwnBound
      (fun i p => (hChildMoment i p).2)
    intro p hp
    apply (hbase p hp).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK0K (sq_nonneg _))
  exact ⟨hmom, fun htime => measure_abs_gt_rpow_le_of_moments hKpos ht htime
    (fun p _ => hY p) (fun p _ => hmom p)⟩

end Problem367

end

end OAI

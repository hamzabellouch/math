import OAI.Probability.FreeIsing.Cavity.MomentRecurrence

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem abs_moment_of_identDistrib_abs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {Y : Ω → ℝ} {Z : Ξ → ℝ}
    (h : IdentDistrib (fun ω => |Z ω|) (fun ω => |Y ω|) ν μ) (p : ℕ) :
    (Integrable (fun ω => |Z ω|^p) ν ↔ Integrable (fun ω => |Y ω|^p) μ) ∧
      (∫ ω, |Z ω|^p ∂ν) = ∫ ω, |Y ω|^p ∂μ := by
  have hp := h.comp (measurable_id.pow_const p)
  exact ⟨hp.integrable_iff, hp.integral_eq⟩

theorem response_abs_moment_of_identDistrib_abs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {Y : Ω → ℝ} {Z : Ξ → ℝ}
    (h : IdentDistrib (fun ω => |Z ω|) (fun ω => |Y ω|) ν μ)
    {theta : ℝ} {psi : ℝ → ℝ}
    (hpsi : Measurable psi) (hZ : Measurable Z)
    (hcontract : ∀ z, |psi z| ≤ theta * |z|) (p : ℕ)
    (hint : Integrable (fun ω => |Y ω|^p) μ) :
    Integrable (fun ω => |psi (Z ω)|^p) ν ∧
      (∫ ω, |psi (Z ω)|^p ∂ν) ≤ theta^p * ∫ ω, |Y ω|^p ∂μ := by
  obtain ⟨hi, heq⟩ := abs_moment_of_identDistrib_abs h p
  have hZi := hi.mpr hint
  have hbound : ∀ ω, |psi (Z ω)|^p ≤ theta^p * |Z ω|^p := by
    intro ω
    simpa only [mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (hcontract (Z ω)) p
  have hpi : Integrable (fun ω => |psi (Z ω)|^p) ν := by
    apply (hZi.const_mul (theta^p)).mono' ((hpsi.comp hZ).abs.pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      change ‖|psi (Z ω)|^p‖ ≤ theta^p * |Z ω|^p
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (psi (Z ω))) p)]
      exact hbound ω
  refine ⟨hpi, ?_⟩
  calc
    _ ≤ ∫ ω, theta^p * |Z ω|^p ∂ν := integral_mono hpi (hZi.const_mul _) hbound
    _ = theta^p * ∫ ω, |Y ω|^p ∂μ := by rw [integral_const_mul, heq]

theorem iIndepFun_cavity_response
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} {b : ℕ}
    {Z : Fin (b + 1) → Ξ → ℝ} (hZ : iIndepFun Z ν)
    {psi : ℝ → ℝ} (hpsi : Measurable psi) :
    iIndepFun (fun (i : Fin (b + 1)) (ω : Ξ) => Fin.cases (motive := fun _ => ℝ) (Z 0 ω) (fun j => psi (Z j.succ ω)) i) ν := by
  have hm : ∀ i : Fin (b + 1), Measurable (fun x : ℝ =>
      Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) := by
    intro i
    exact Fin.cases measurable_id (fun _ => hpsi) i
  have hh := hZ.comp (fun (i : Fin (b + 1)) (x : ℝ) =>
    Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) hm
  have hfun : (fun i => (fun x : ℝ => Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) ∘ Z i) =
      (fun (i : Fin (b + 1)) (ω : Ξ) => Fin.cases (motive := fun _ => ℝ)
        (Z 0 ω) (fun j => psi (Z j.succ ω)) i) := by
    funext i ω
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  rw [hfun] at hh
  exact hh

theorem exists_critical_all_moments_of_response_recursion
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta K0 t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK0 : 0 ≤ K0) (ht : 0 < t)
    {Y : Ω → ℝ} {Ycond : Ξ → ℝ} {Z : Fin (b + 1) → Ξ → ℝ}
    {psi : ℝ → ℝ} (hpsi : Measurable psi) (hcontract : ∀ z, |psi z| ≤ theta * |z|)
    (hY : ∀ p : ℕ, Integrable (fun ω => |Y ω|^p) μ)
    (hOwnInt : ∀ p : ℕ, Integrable (fun ω => |Z 0 ω|^p) ν)
    (hZ : iIndepFun Z ν) (hmZ : ∀ i, Measurable (Z i))
    (hCond : IdentDistrib (fun ω => |Ycond ω|) (fun ω => |Y ω|) ν μ)
    (hChild : ∀ i : Fin b,
      IdentDistrib (fun ω => |Z i.succ ω|) (fun ω => |Y ω|) ν μ)
    (hEq : ∀ᵐ ω ∂ν, Ycond ω =
      ∑ i : Fin (b + 1), Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i)
    (hOwn : ∀ p : ℕ, (∫ ω, |Z 0 ω|^p ∂ν) ≤
      Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4))
    (hbase : ∀ p : ℕ, p < 3 → (∫ ω, |Y ω|^p ∂μ) ≤
      Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 ≤ K ∧
      ∀ p : ℕ, (∫ ω, |Y ω|^p ∂μ) ≤
        Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  let X : Fin (b + 1) → Ξ → ℝ :=
    fun i ω => Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i
  have hXi : iIndepFun X ν := iIndepFun_cavity_response hZ hpsi
  have hmX : ∀ i, Measurable (X i) := by
    intro i
    refine Fin.cases (hmZ 0) (fun j => hpsi.comp (hmZ j.succ)) i
  have hChildMoment (i : Fin b) (p : ℕ) :=
    response_abs_moment_of_identDistrib_abs (hChild i) hpsi (hmZ i.succ) hcontract p (hY p)
  have hMom : ∀ i (p : ℕ), Integrable (fun ω => |X i ω|^p) ν := by
    intro i p
    exact Fin.cases (hOwnInt p) (fun j => (hChildMoment j p).1) i
  have hRec : ∀ p : ℕ, (∫ ω, |Y ω|^p ∂μ) ≤ ∫ ω, |∑ i, X i ω|^p ∂ν := by
    intro p
    apply le_of_eq
    calc
      _ = ∫ ω, |Ycond ω|^p ∂ν := (abs_moment_of_identDistrib_abs hCond p).2.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hEq] with ω hω
        exact congrArg (fun x : ℝ => |x|^p) hω)
  exact exists_critical_all_moments_bound htheta htheta1 hcritical hK0 ht
    (fun p => ∫ ω, |Y ω|^p ∂μ) hXi hmX hMom hRec hOwn
    (fun i p => (hChildMoment i p).2) hbase

theorem exists_uniform_critical_response_moment_and_tail_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK0 : 0 < K0)
    (S : Set ℝ) (ht : ∀ t ∈ S, 0 < t)
    (Y : ℝ → Ω → ℝ) (Ycond : ℝ → Ξ → ℝ)
    (Z : ℝ → Fin (b + 1) → Ξ → ℝ)
    {psi : ℝ → ℝ} (hpsi : Measurable psi) (hcontract : ∀ z, |psi z| ≤ theta * |z|)
    (hY : ∀ t ∈ S, ∀ p : ℕ, Integrable (fun ω => |Y t ω|^p) μ)
    (hOwnInt : ∀ t ∈ S, ∀ p : ℕ, Integrable (fun ω => |Z t 0 ω|^p) ν)
    (hZ : ∀ t ∈ S, iIndepFun (Z t) ν)
    (hmZ : ∀ t ∈ S, ∀ i, Measurable (Z t i))
    (hCond : ∀ t ∈ S,
      IdentDistrib (fun ω => |Ycond t ω|) (fun ω => |Y t ω|) ν μ)
    (hChild : ∀ t ∈ S, ∀ i : Fin b,
      IdentDistrib (fun ω => |Z t i.succ ω|) (fun ω => |Y t ω|) ν μ)
    (hEq : ∀ t ∈ S, ∀ᵐ ω ∂ν, Ycond t ω =
      ∑ i : Fin (b + 1), Fin.cases (Z t 0 ω) (fun j => psi (Z t j.succ ω)) i)
    (hOwn : ∀ t ∈ S, ∀ p : ℕ, (∫ ω, |Z t 0 ω|^p ∂ν) ≤
      Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4))
    (hbase : ∀ t ∈ S, ∀ p : ℕ, p < 3 → (∫ ω, |Y t ω|^p ∂μ) ≤
      Real.exp (K0 * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 < K ∧
      (∀ t ∈ S, ∀ p : ℕ, (∫ ω, |Y t ω|^p ∂μ) ≤
        Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) ∧
      (∀ t ∈ S, 32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y t ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t)^2) / (512 * K)))) := by
  let X : ℝ → Fin (b + 1) → Ξ → ℝ :=
    fun t i ω => Fin.cases (Z t 0 ω) (fun j => psi (Z t j.succ ω)) i
  have hXi : ∀ t ∈ S, iIndepFun (X t) ν :=
    fun t htS => iIndepFun_cavity_response (hZ t htS) hpsi
  have hmX : ∀ t ∈ S, ∀ i, Measurable (X t i) := by
    intro t htS i
    exact Fin.cases (hmZ t htS 0) (fun j => hpsi.comp (hmZ t htS j.succ)) i
  have hChildMoment (t : ℝ) (htS : t ∈ S) (i : Fin b) (p : ℕ) :=
    response_abs_moment_of_identDistrib_abs (hChild t htS i) hpsi (hmZ t htS i.succ)
      hcontract p (hY t htS p)
  have hMom : ∀ t ∈ S, ∀ i (p : ℕ), Integrable (fun ω => |X t i ω|^p) ν := by
    intro t htS i p
    exact Fin.cases (hOwnInt t htS p) (fun j => (hChildMoment t htS j p).1) i
  have hRec : ∀ t ∈ S, ∀ p : ℕ,
      (∫ ω, |Y t ω|^p ∂μ) ≤ ∫ ω, |∑ i, X t i ω|^p ∂ν := by
    intro t htS p
    apply le_of_eq
    calc
      _ = ∫ ω, |Ycond t ω|^p ∂ν :=
        (abs_moment_of_identDistrib_abs (hCond t htS) p).2.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hEq t htS] with ω hω
        exact congrArg (fun x : ℝ => |x|^p) hω)
  exact exists_uniform_critical_moment_and_tail_bound htheta htheta1 hcritical hK0 S ht
    Y X hY hXi hmX hMom hRec hOwn (fun t htS i p => (hChildMoment t htS i p).2) hbase

end Problem367

end OAI

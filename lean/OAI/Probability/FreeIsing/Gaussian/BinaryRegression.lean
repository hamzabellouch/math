import OAI.Probability.FreeIsing.Conditioning.Product
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.BinaryRegression

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → IsingSpin}

private theorem spin_event_measurable (hS : Measurable S) (s : IsingSpin) :
    MeasurableSet {ω | S ω = s} := by
  exact hS (by trivial : MeasurableSet ({s} : Set IsingSpin))

theorem integral_spin_function (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (φ : IsingSpin → ℝ) :
    (∫ ω, φ (S ω) ∂μ) = (φ IsingSpin.neg + φ IsingSpin.pos) / 2 := by
  classical
  have hneg := spin_event_measurable hS IsingSpin.neg
  have hpos := spin_event_measurable hS IsingSpin.pos
  have hf : (fun ω => φ (S ω)) =
      {ω | S ω = IsingSpin.neg}.indicator (fun _ => φ IsingSpin.neg) +
      {ω | S ω = IsingSpin.pos}.indicator (fun _ => φ IsingSpin.pos) := by
    funext ω
    cases hs : S ω <;> simp [hs]
  rw [hf]
  change (∫ ω, ({ω | S ω = IsingSpin.neg}.indicator (fun _ => φ IsingSpin.neg)) ω +
    ({ω | S ω = IsingSpin.pos}.indicator (fun _ => φ IsingSpin.pos)) ω ∂μ) = _
  rw [integral_add ((integrable_const _).indicator hneg)
    ((integrable_const _).indicator hpos), integral_indicator hneg,
    integral_indicator hpos, setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, measureReal_def, hfair]
  norm_num
  ring

theorem exists_mul_spinSign_of_centered (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hf : Measurable[isingSpinMeasurable.comap S] f)
    (hzero : ∫ ω, f ω ∂μ = 0) :
    ∃ a : ℝ, ∀ ω, f ω = a * spinSign (S ω) := by
  obtain ⟨φ, hφ, rfl⟩ := hf.exists_eq_measurable_comp
  have hm := integral_spin_function hS hfair φ
  have hs : φ IsingSpin.neg + φ IsingSpin.pos = 0 := by
    simp only [Function.comp_apply] at hzero
    rw [hzero] at hm
    linarith
  refine ⟨φ IsingSpin.pos, ?_⟩
  intro ω
  cases he : S ω with
  | neg =>
    simp [Function.comp_apply, he, spinSign]
    linarith
  | pos => simp [Function.comp_apply, he, spinSign]

theorem exists_condExp_mul_spinSign (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hzero : ∫ ω, f ω ∂μ = 0) :
    ∃ a : ℝ, ∀ ω, μ[f | isingSpinMeasurable.comap S] ω = a * spinSign (S ω) := by
  apply exists_mul_spinSign_of_centered hS hfair stronglyMeasurable_condExp.measurable
  rw [integral_condExp hS.comap_le, hzero]

theorem exists_condExp_mul_spinSign_sq_le (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hzero : ∫ ω, f ω ∂μ = 0)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) :
    ∃ a : ℝ, (∀ ω, μ[f | isingSpinMeasurable.comap S] ω = a * spinSign (S ω)) ∧
      a^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  obtain ⟨a, ha⟩ := exists_condExp_mul_spinSign hS hfair hzero
  refine ⟨a, ha, ?_⟩
  have hint : Integrable (fun ω => ‖f ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hf2
  have hb := integral_norm_condExp_rpow_le (μ := μ) (m := isingSpinMeasurable.comap S)
    (by norm_num : (1 : ℝ) ≤ 2) hint
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ha, mul_pow, spinSign_sq, mul_one] at hb
  simpa using hb

theorem abs_correlation_le_of_binary_condExp {T : Ω → IsingSpin}
    (hS : Measurable S) (hT : Measurable T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) (hg2 : Integrable (fun ω => (g ω)^2) μ)
    (hfactor : (∫ ω, f ω * g ω ∂μ) = ∫ ω,
      μ[f | isingSpinMeasurable.comap S] ω * μ[g | isingSpinMeasurable.comap T] ω ∂μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  obtain ⟨a, ha, hsa⟩ := exists_condExp_mul_spinSign_sq_le hS hSfair hfzero hf2
  obtain ⟨b, hb, hsb⟩ := exists_condExp_mul_spinSign_sq_le hT hTfair hgzero hg2
  have hfa : 0 ≤ ∫ ω, (f ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hgb : 0 ≤ ∫ ω, (g ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ha' : |a| ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
    apply (Real.le_sqrt (abs_nonneg a) hfa).2
    simpa only [sq_abs] using hsa
  have hb' : |b| ≤ Real.sqrt (∫ ω, (g ω)^2 ∂μ) := by
    apply (Real.le_sqrt (abs_nonneg b) hgb).2
    simpa only [sq_abs] using hsb
  have heq : (∫ ω, f ω * g ω ∂μ) =
      (a*b) * ∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ := by
    rw [hfactor, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    rw [ha, hb]
    ring
  rw [heq, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul ha' hb' (abs_nonneg b) (Real.sqrt_nonneg _)) (abs_nonneg _)

theorem abs_correlation_le_of_endpoint_condIndep [StandardBorelSpace Ω]
    {T : Ω → IsingSpin} {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hS : Measurable[mΩ] S) (hT : Measurable[mΩ] T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hind : ProbabilityTheory.CondIndepFun m hm f g μ)
    (hleft : μ[f | m] =ᵐ[μ] μ[f | isingSpinMeasurable.comap S])
    (hright : μ[g | m] =ᵐ[μ] μ[g | isingSpinMeasurable.comap T]) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  let : MeasurableSpace Ω := mΩ
  apply abs_correlation_le_of_binary_condExp hS hT hSfair hTfair hfzero hgzero
    hf2.integrable_sq hg2.integrable_sq
  calc
    (∫ ω, f ω * g ω ∂μ) = ∫ ω, μ[f | m] ω * μ[g | m] ω ∂μ :=
      integral_mul_eq_integral_condExp_mul_of_condIndepFun hm hind hf hg
        (hf2.integrable (by norm_num)) (hg2.integrable (by norm_num))
        ((hf2.integrable_mul hg2).congr (Filter.Eventually.of_forall fun _ => rfl))
    _ = ∫ ω, μ[f | isingSpinMeasurable.comap S] ω *
        μ[g | isingSpinMeasurable.comap T] ω ∂μ :=
      integral_congr_ae (hleft.mul hright)

theorem abs_correlation_le_of_spatial_condIndep [StandardBorelSpace Ω]
    {T : Ω → IsingSpin} (hS : Measurable S) (hT : Measurable T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hind : ProbabilityTheory.CondIndepFun
      (isingSpinMeasurable.comap S ⊔ isingSpinMeasurable.comap T)
      (sup_le hS.comap_le hT.comap_le) f g μ)
    (hleft : ProbabilityTheory.CondIndepFun (isingSpinMeasurable.comap S) hS.comap_le T f μ)
    (hright : ProbabilityTheory.CondIndepFun (isingSpinMeasurable.comap T) hT.comap_le S g μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  let : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
  apply abs_correlation_le_of_endpoint_condIndep (sup_le hS.comap_le hT.comap_le)
    hS hT hSfair hTfair hf hg hfzero hgzero hf2 hg2 hind
  · exact condExp_sup_eq_of_condIndepFun hS hT hf (hf2.integrable (by norm_num)) hleft
  · simpa only [sup_comm] using
      condExp_sup_eq_of_condIndepFun hT hS hg (hg2.integrable (by norm_num)) hright

end Problem367.BinaryRegression

end

end OAI

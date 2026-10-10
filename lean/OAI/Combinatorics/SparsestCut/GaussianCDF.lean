import OAI.Combinatorics.SparsestCut.GaussianPoincare

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianCDF
local notation "μ" => gaussianReal 0 1
def Φ (x : ℝ) : ℝ := cdf μ x
def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos _ _ _ (by norm_num)
lemma φ_contDiff : ContDiff ℝ ∞ φ := by unfold φ gaussianPDFReal; fun_prop
lemma φ_integrable : Integrable φ := integrable_gaussianPDFReal _ _
lemma Φ_integral (x : ℝ) : Φ x = ∫ t in Iic x, φ t := by
  rw [Φ, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg (0:ℝ) 1 t))

lemma Φ_primitive (x : ℝ) : Φ x = Φ 0 + ∫ t in (0:ℝ)..x, φ t := by
  rw [Φ_integral, Φ_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (φ_integrable.integrableOn (s := Iic 0)) (φ_integrable.integrableOn (s := Iic x))
  linarith

lemma Φ_hasDeriv (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (φ_contDiff.continuous.intervalIntegrable (0:ℝ) x)
    φ_contDiff.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    φ_contDiff.continuous.continuousAt
  have h' := h.const_add (Φ 0)
  convert h' using 1
  first | rfl | exact funext Φ_primitive

lemma Φ_continuous : Continuous Φ := continuous_iff_continuousAt.mpr (fun x => (Φ_hasDeriv x).continuousAt)
lemma Φ_strictMono : StrictMono Φ := strictMono_of_deriv_pos (fun x => by rw [(Φ_hasDeriv x).deriv]; exact φ_pos x)
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := by
  constructor
  · exact (cdf_nonneg μ (x-1)).trans_lt (Φ_strictMono (by linarith))
  · exact (Φ_strictMono (show x < x+1 by linarith)).trans_le (cdf_le_one μ (x+1))

lemma Φ_surj {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) : ∃ x, Φ x = y := by
  apply intermediate_value_univ₂_eventually₂ (l₁ := atBot) (l₂ := atTop) Φ_continuous continuous_const
  · exact (tendsto_cdf_atBot μ).eventually (eventually_le_nhds hy.1)
  · exact (tendsto_cdf_atTop μ).eventually (eventually_ge_nhds hy.2)

lemma Φ_map : (μ).map Φ = volume.restrict (Ioo (0:ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply Φ_continuous.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases h0 : y ≤ 0
  · have he : Φ ⁻¹' Iic y = ∅ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (h0.trans_lt (Φ_mem x).1)
    have he' : Iic y ∩ Ioo (0:ℝ) 1 = ∅ := by ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]; grind
    rw [he, he', measure_empty, measure_empty]
  by_cases h1 : 1 ≤ y
  · have he : Φ ⁻¹' Iic y = univ := by ext x; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (Φ_mem x).2.le.trans h1
    have he' : Iic y ∩ Ioo (0:ℝ) 1 = Ioo (0:ℝ) 1 := by ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]; constructor <;> grind
    rw [he, he', measure_univ, Real.volume_Ioo]; norm_num
  obtain ⟨x,hx⟩ := Φ_surj ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
  have he : Φ ⁻¹' Iic y = Iic x := by ext z; simpa only [mem_preimage, mem_Iic, ← hx] using Φ_strictMono.le_iff_le
  have he' : Iic y ∩ Ioo (0:ℝ) 1 = Ioc (0:ℝ) y := by
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]; grind
  rw [he, he', ← ofReal_cdf μ x, Real.volume_Ioc, sub_zero, ← hx]
  rfl

def ψ (x : ℝ) : ℝ := 2*Φ x-1
lemma ψ_hasDeriv (x : ℝ) : HasDerivAt ψ (2*φ x) x := (Φ_hasDeriv x).const_mul 2 |>.sub_const 1
lemma ψ_mem (x : ℝ) : ψ x ∈ Ioo (-1:ℝ) 1 := by
  have h := Φ_mem x
  dsimp [ψ]; constructor <;> linarith [h.1,h.2]

lemma ψ_contDiff : ContDiff ℝ 1 ψ := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (ψ_hasDeriv x).differentiableAt
  · have he : deriv ψ = fun x => 2*φ x := funext (fun x => (ψ_hasDeriv x).deriv)
    rw [he]
    exact continuous_const.mul φ_contDiff.continuous

lemma ψ_deriv_bound (x : ℝ) : |2*φ x| ≤ 1 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hge : 2 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have he0 : 0 ≤ Real.exp (-x^2/2) := (Real.exp_pos _).le
  rw [abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (φ_pos x))]
  change 2*((Real.sqrt (2*Real.pi*1))⁻¹*Real.exp (-(x-0)^2/(2*1))) ≤ 1
  simp only [mul_one, sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹*(2*Real.exp (-x^2/2)) := by ring
    _ ≤ 1 := (inv_mul_le_iff₀ hs).mpr (by nlinarith)

def uniform : Measure ℝ := (2:ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1:ℝ) 1)

lemma ψ_map : (μ).map ψ = uniform := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply ψ_contDiff.continuous.measurable measurableSet_Iic]
  change μ (ψ ⁻¹' Iic y) = (2:ℝ≥0∞)⁻¹ * (volume.restrict (Ioo (-1:ℝ) 1)) (Iic y)
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases h0 : y ≤ -1
  · have he : ψ ⁻¹' Iic y = ∅ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (h0.trans_lt (ψ_mem x).1)
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]; grind
    simp [he,he']
  by_cases h1 : 1 ≤ y
  · have he : ψ ⁻¹' Iic y = univ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (ψ_mem x).2.le.trans h1
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioo (-1:ℝ) 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]; constructor <;> grind
    rw [he,he',measure_univ,Real.volume_Ioo]; norm_num;
    exact (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
  have hy : (y+1)/2 ∈ Ioo (0:ℝ) 1 := by constructor <;> linarith
  obtain ⟨x,hx⟩ := Φ_surj hy
  have he : ψ ⁻¹' Iic y = Iic x := by
    ext z
    simp only [mem_preimage, mem_Iic, ψ]
    rw [show y = 2*Φ x-1 by linarith]
    rw [show 2*Φ z-1 ≤ 2*Φ x-1 ↔ Φ z ≤ Φ x by constructor <;> intro hn <;> linarith]
    exact Φ_strictMono.le_iff_le
  have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioc (-1:ℝ) y := by
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]; grind
  rw [he,he',← ofReal_cdf μ x,Real.volume_Ioc]
  change ENNReal.ofReal (Φ x) = (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal (y- -1)
  rw [hx,show y- -1 = y+1 by ring,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  simp [div_eq_mul_inv,mul_comm]

instance uniform_probability : IsProbabilityMeasure uniform := by
  rw [← ψ_map]
  infer_instance

end UniformSparsestCut.GaussianCDF

end

end OAI

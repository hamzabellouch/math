import OAI.Analysis.FreeEntropy.RandomHeatMoments

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem integral_sq_le_integral_square {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x,f x ∂μ)^2 ≤ ∫x,(f x)^2 ∂μ := by
  let m := ∫x,f x ∂μ
  have h : 0≤∫x,(f x-m)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (f x-m))
  have he : (fun x => (f x-m)^2) = fun x => (f x)^2-2*m*f x+m^2 := by funext x; ring
  rw [he] at h
  have ha := integral_add (hf2.sub (hf.const_mul (2*m))) (integrable_const (m^2))
  simp only [Pi.sub_apply] at ha
  rw [ha,integral_sub hf2 (hf.const_mul (2*m)),integral_const_mul] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  dsimp only [m] at h
  nlinarith
 theorem complex_integral_error_sq_le {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (c : ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x-c‖^2) μ) :
    ‖(∫x,f x ∂μ)-c‖^2 ≤ ∫x,‖f x-c‖^2 ∂μ := by
  have hi := hf.sub (integrable_const c)
  have h : ‖(∫x,f x ∂μ)-c‖ ≤ ∫x,‖f x-c‖ ∂μ := by
    have hh := norm_integral_le_integral_norm (fun x => f x-c) (μ := μ)
    simpa only [integral_sub hf (integrable_const c),integral_const,probReal_univ,one_smul] using hh
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (integral_sq_le_integral_square μ hi.norm hf2)
 theorem complex_integral_error_le {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (c : ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x-c‖^2) μ) :
    ‖(∫x,f x ∂μ)-c‖ ≤ Real.sqrt (∫x,‖f x-c‖^2 ∂μ) := by
  exact (Real.le_sqrt (norm_nonneg _) (integral_nonneg (fun x => sq_nonneg _))).mpr
    (complex_integral_error_sq_le μ c hf hf2)
 theorem complex_integral_tendsto_of_L2 {Ω : ℕ → Type u4} [∀k,MeasurableSpace (Ω k)]
    (μ : (k:ℕ) → Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)] (f : (k:ℕ) → Ω k → ℂ) (c : ℂ)
    (hi : ∀k,Integrable (f k) (μ k)) (hi2 : ∀k,Integrable (fun x => ‖f k x-c‖^2) (μ k))
    (ht : Tendsto (fun k => ∫x,‖f k x-c‖^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫x,f k x ∂μ k) atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff]
  exact squeeze_zero_norm (fun k => complex_integral_error_le (μ k) c (hi k) (hi2 k)) (by simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht)
 theorem complex_mul_integrable_of_squares {Ω : Type u5} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => ‖f x‖^2) μ) (hg2 : Integrable (fun x => ‖g x‖^2) μ) :
    Integrable (fun x => f x*g x) μ := by
  apply ((hf2.add hg2).div_const 2).mono' (hf.mul hg)
  exact ae_of_all _ (fun x => by dsimp; rw [norm_mul]; nlinarith [sq_nonneg (‖f x‖-‖g x‖)])
 theorem complex_integral_mul_centered_bound {Ω : Type u6} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => ‖f x‖^2) μ) (hg2 : Integrable (fun x => ‖g x‖^2) μ) :
    ‖∫x,f x*g x ∂μ‖ ≤ ((∫x,‖f x‖^2 ∂μ)+(∫x,‖g x‖^2 ∂μ))/2 := by
  calc
    _ ≤ ∫x,‖f x*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫x,(‖f x‖^2+‖g x‖^2)/2 ∂μ := by
      apply integral_mono (complex_mul_integrable_of_squares μ hf hg hf2 hg2).norm ((hf2.add hg2).div_const 2)
      intro x; dsimp; rw [norm_mul]; nlinarith [sq_nonneg (‖f x‖-‖g x‖)]
    _ = _ := by rw [integral_div,integral_add hf2 hg2]
 theorem complex_integral_mul_tendsto_of_L2 {Ω : ℕ → Type u7} [∀k,MeasurableSpace (Ω k)]
    (μ : (k:ℕ) → Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (f g : (k:ℕ) → Ω k → ℂ) (c d : ℂ)
    (hif : ∀k,Integrable (f k) (μ k)) (hig : ∀k,Integrable (g k) (μ k))
    (hif2 : ∀k,Integrable (fun x => ‖f k x-c‖^2) (μ k))
    (hig2 : ∀k,Integrable (fun x => ‖g k x-d‖^2) (μ k))
    (htf : Tendsto (fun k => ∫x,‖f k x-c‖^2 ∂μ k) atTop (𝓝 0))
    (htg : Tendsto (fun k => ∫x,‖g k x-d‖^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫x,f k x*g k x ∂μ k) atTop (𝓝 (c*d)) := by
  have hcf (k : ℕ) : Integrable (fun x => f k x-c) (μ k) := (hif k).sub (integrable_const c)
  have hcg (k : ℕ) : Integrable (fun x => g k x-d) (μ k) := (hig k).sub (integrable_const d)
  have hr : Tendsto (fun k => ∫x,(f k x-c)*(g k x-d) ∂μ k) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => complex_integral_mul_centered_bound (μ k) (hcf k).aestronglyMeasurable (hcg k).aestronglyMeasurable (hif2 k) (hig2 k))
    simpa using (htf.add htg).div_const 2
  have hf := complex_integral_tendsto_of_L2 μ f c hif hif2 htf
  have hg := complex_integral_tendsto_of_L2 μ g d hig hig2 htg
  have he k : (∫x,f k x*g k x ∂μ k) = (∫x,(f k x-c)*(g k x-d) ∂μ k)+
      ((∫x,f k x ∂μ k)-c)*d+c*((∫x,g k x ∂μ k)-d)+c*d := by
    have hmul := complex_mul_integrable_of_squares (μ k) (hcf k).aestronglyMeasurable (hcg k).aestronglyMeasurable (hif2 k) (hig2 k)
    have hpoint : (fun x => f k x*g k x) = fun x => (f k x-c)*(g k x-d)+(f k x-c)*d+c*(g k x-d)+c*d := by funext x; ring
    have ha := integral_add ((hmul.add ((hcf k).mul_const d)).add ((hcg k).const_mul c)) (integrable_const (c*d))
    have hb := integral_add (hmul.add ((hcf k).mul_const d)) ((hcg k).const_mul c)
    simp only [Pi.add_apply] at ha hb
    rw [hpoint,ha,hb,
      integral_add hmul ((hcf k).mul_const d),integral_mul_const,integral_const_mul,
      integral_sub (hif k) (integrable_const c),integral_sub (hig k) (integrable_const d)]
    simp only [integral_const,probReal_univ,one_smul]
  simp_rw [he]
  convert ((hr.add ((hf.sub_const c).mul_const d)).add ((hg.sub_const d).const_mul c)).add_const (c*d) using 1 ; simp
end FiniteEntropySeparation

end

end OAI

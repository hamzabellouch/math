import Mathlib

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

def rescaleSchwartz (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E,F) →L[ℂ] 𝓢(E,F) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr))).comp
      (SchwartzMap.compSubConstCLM ℂ (-p))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_apply (p x : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F)) :
    rescaleSchwartz p r hr f x = f (r • x + p) := by
  simp [rescaleSchwartz, Units.smul_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_derivative (p : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F)) (v : E) :
    ∂_{v} (rescaleSchwartz p r hr f) = r • rescaleSchwartz p r hr (∂_{v} f) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (rescaleSchwartz p r hr f : E → F) = fun y => f (r • y + p) := by
    funext y; exact rescaleSchwartz_apply p y r hr f
  have hd := (f.hasFDerivAt (r • x + p)).comp x
    (((hasFDerivAt_id x).const_smul r).add_const p)
  dsimp only [Function.comp_def,Pi.smul_apply,id_eq] at hd
  rw [he,hd.fderiv]
  simp [rescaleSchwartz_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv]

omit [CompleteSpace F] in
lemma rescaleSchwartz_norm (p : E) {r : ℝ} (hr : 0 < r) (q : ENNReal)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp q (volume : Measure E)‖ =
      ((r ^ Module.finrank ℝ E)⁻¹)^((1/q).toReal) * ‖f.toLp q (volume : Measure E)‖ := by
  have hm := eLpNorm_map_measure (p := q)
    ((f.continuous.comp (continuous_id.add_const p)).aestronglyMeasurable
      (μ := Measure.map (fun x : E => r • x) volume))
    (measurable_const_smul r).aemeasurable
  rw [Measure.map_addHaar_smul volume hr.ne',
    eLpNorm_smul_measure_of_ne_top hq _ _
      (f.continuous.comp (continuous_id.add_const p)).aestronglyMeasurable] at hm
  have ht := eLpNorm_comp_measurePreserving (p := q) f.continuous.aestronglyMeasurable
    (measurePreserving_add_right (volume : Measure E) p)
  have ht' : eLpNorm (fun x => f (x+p)) q (volume : Measure E) = eLpNorm f q volume := ht
  change ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| ^ (1 / q).toReal *
    eLpNorm (fun x => f (x+p)) q volume =
    eLpNorm (fun x => f (r • x+p)) q volume at hm
  rw [ht'] at hm
  have he : (fun x => f (r • x+p)) = (rescaleSchwartz p r hr.ne' f : E → F) := by
    funext x; exact (rescaleSchwartz_apply p x r hr.ne' f).symm
  rw [he] at hm
  rw [SchwartzMap.norm_toLp,← hm,SchwartzMap.norm_toLp]
  simp only [ENNReal.toReal_mul,← ENNReal.toReal_rpow,
    abs_of_pos (inv_pos.mpr (pow_pos hr _)),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _))]

omit [CompleteSpace F] in
lemma rescaleSchwartz_L2 (hdim : Module.finrank ℝ E = 4)
    (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp 2 (volume : Measure E)‖ =
      (r^2)⁻¹ * ‖f.toLp 2 (volume : Measure E)‖ := by
  rw [rescaleSchwartz_norm p hr 2 (by norm_num),hdim]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  congr 1
  rw [Real.inv_rpow (by positivity : 0 ≤ r^4)]
  congr 1
  rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr.le]
  norm_num

omit [CompleteSpace F] in
lemma rescaleSchwartz_L4 (hdim : Module.finrank ℝ E = 4)
    (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp 4 (volume : Measure E)‖ =
      r⁻¹ * ‖f.toLp 4 (volume : Measure E)‖ := by
  rw [rescaleSchwartz_norm p hr 4 (by norm_num),hdim]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  congr 1
  rw [Real.inv_rpow (by positivity : 0 ≤ r^4)]
  congr 1
  rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr.le]
  norm_num

omit [CompleteSpace F] in
lemma schwartz_cutoff_L2_L4 (χ : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    ‖(SchwartzMap.smulLeftCLM F χ f).toLp 2 (volume : Measure E)‖ ≤
      ‖χ.toLp 4 (volume : Measure E)‖ * ‖f.toLp 4 (volume : Measure E)‖ := by
  have : (4:ENNReal).HolderTriple 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hh := eLpNorm_smul_le_mul_eLpNorm (μ := (volume : Measure E)) (p := 4) (q := 4) (r := 2)
    χ.continuous.aestronglyMeasurable f.continuous.aestronglyMeasurable
  have he : (χ : E → ℂ) • (f : E → F) = (SchwartzMap.smulLeftCLM F χ f : E → F) := by
    ext x; simp [χ.hasTemperateGrowth]
  rw [he] at hh
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (χ.memLp 4 volume).ne (f.memLp 4 volume).ne) hh
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul] using h

omit [CompleteSpace F] in
lemma schwartz_cutoff_L2_L2 (χ : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    ‖(SchwartzMap.smulLeftCLM F χ f).toLp 2 (volume : Measure E)‖ ≤
      SchwartzMap.seminorm ℂ 0 0 χ * ‖f.toLp 2 (volume : Measure E)‖ := by
  let C := SchwartzMap.seminorm ℂ 0 0 χ
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb : ∀ᵐ x ∂(volume : Measure E), ‖(SchwartzMap.smulLeftCLM F χ f) x‖ ≤ C*‖f x‖ := by
    filter_upwards [] with x
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,norm_smul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ χ x) (norm_nonneg _)
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (SchwartzMap.smulLeftCLM F χ f).continuous.aestronglyMeasurable hb 2
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp 2 volume).ne) he
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] using h
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI

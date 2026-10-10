import Mathlib
import OAI.Probability.LogConcave.Sampling.PairGauge

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

lemma probabilityFlow_growth {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) (z : Point d) :
    ‖fullProbabilityFlow hF x hr hl T z‖≤circuitGrowthConstant*(circuitD F x+‖z‖) := by
  have hf := probabilityFlow_initial_displacement hF x hr hl z ⟨hT,hT1.le⟩
  have hn := norm_le_norm_sub_add (fullProbabilityFlow hF x hr hl T z) z
  rw [field_zero_eq_gradient] at hf
  have hD : ‖gradient F x‖≤circuitD F x := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hd := sqrt_le_circuitD F x
  have hc := circuitD_nonneg F x
  have h₁ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg (gradient F x))
  have h₂ := mul_le_mul_of_nonneg_right (show (lam:ℝ)*r^2≤1 by linarith)
    (show 0≤Real.pi*Real.sqrt d+‖z‖ by positivity)
  have hp := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have hb : r*‖gradient F x‖+((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖)≤
      (Real.pi+1)*(circuitD F x+‖z‖) := by
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z)]
  have hh := mul_le_mul_of_nonneg_left hb terminalTransportConstant_pos.le
  have hz : ‖z‖≤(Real.pi+1)*(circuitD F x+‖z‖) := by
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z),mul_nonneg Real.pi_pos.le hc]
  have hc' : terminalTransportConstant+1≤8*(terminalTransportConstant+1) := by
    linarith [terminalTransportConstant_pos]
  have hh' := mul_le_mul_of_nonneg_right hc' (show 0≤(Real.pi+1)*(circuitD F x+‖z‖) by positivity)
  dsimp [circuitGrowthConstant]
  nlinarith

lemma interpolationLaw_norm_sq {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) :
    Integrable (fun z : Point d => ‖z‖^2) (interpolationLaw F x r T) ∧
    (∫z : Point d,‖z‖^2 ∂interpolationLaw F x r T)≤4*circuitGrowthConstant^2*(circuitD F x)^2 := by
  have hm := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT,hT1.le⟩).continuous.measurable
  have hg := gaussian_growth_sq_moment (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT,hT1.le⟩).continuous
    circuitGrowthConstant_pos.le (circuitD_nonneg F x)
    (probabilityFlow_growth hF x hr hr1 hl hT hT1)
  rw [←fullProbabilityFlow_interpolation_closed hF x hr hl hT hT1]
  refine ⟨(integrable_map_measure (by fun_prop) hm.aemeasurable).mpr hg.1,?_⟩
  rw [integral_map hm.aemeasurable (by fun_prop)]
  apply hg.2.trans
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg circuitGrowthConstant)]

lemma pairGauge_sq_bound {C : ℝ} (hC : 0≤C) (z : Point d × Point d) :
    (pairGauge C z)^2≤4*(1+C)^2+4*‖z.1‖^2+4*‖z.2‖^2 := by
  have hp : ‖z‖≤‖z.1‖+‖z.2‖ := by
    change max ‖z.1‖ ‖z.2‖≤_
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hq : 0≤pairGauge C z := by unfold pairGauge; positivity
  have hb : pairGauge C z≤1+C+‖z.1‖+‖z.2‖ := by dsimp [pairGauge]; linarith
  have hh := pow_le_pow_left₀ hq hb 2
  nlinarith [sq_nonneg (1+C-‖z.1‖-‖z.2‖),sq_nonneg (‖z.1‖-‖z.2‖)]

lemma pairGauge_moment (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : Point d => ‖z‖^2) μ) {C : ℝ} (hC : 0≤C) :
    Integrable (fun z => (pairGauge C z)^2) (μ.prod (stdGaussian (Point d))) ∧
    (∫z,(pairGauge C z)^2 ∂μ.prod (stdGaussian (Point d)))≤
      4*(1+C)^2+4*(∫z,‖z‖^2 ∂μ)+4*d := by
  have hj : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable_sq
  have hdom : Integrable (fun z : Point d × Point d => 4*(1+C)^2+4*‖z.1‖^2+4*‖z.2‖^2)
      (μ.prod (stdGaussian (Point d))) := ((integrable_const (4*(1+C)^2)).add ((hi.comp_fst (stdGaussian (Point d))).const_mul 4)).add
    ((hj.comp_snd μ).const_mul 4)
  have hgi : Integrable (fun z => (pairGauge C z)^2) (μ.prod (stdGaussian (Point d))) := by
    apply hdom.mono' ((pairGauge_measurable C).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using pairGauge_sq_bound hC z)
  refine ⟨hgi,?_⟩
  apply (integral_mono hgi hdom (pairGauge_sq_bound hC)).trans_eq
  have hf : Integrable (fun z : Point d × Point d => 4*‖z.1‖^2) (μ.prod (stdGaussian (Point d))) := (hi.comp_fst _).const_mul _
  have hs : Integrable (fun z : Point d × Point d => 4*‖z.2‖^2) (μ.prod (stdGaussian (Point d))) := (hj.comp_snd _).const_mul _
  have hl : Integrable (fun z : Point d × Point d => 4*(1+C)^2+4*‖z.1‖^2) (μ.prod (stdGaussian (Point d))) := (integrable_const _).add hf
  rw [integral_add hl hs,integral_add (integrable_const _) hf,integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_const_mul]
  rw [integral_fun_fst (fun z : Point d => ‖z‖^2),integral_fun_snd (fun z : Point d => ‖z‖^2)]
  simp only [probReal_univ,one_smul,stdGaussian_sq_norm]

lemma pairGauge_interpolation_moment {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) (hd : 1≤d) :
    Integrable (fun z => (pairGauge (circuitD F x) z)^2)
      ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
    (∫z,(pairGauge (circuitD F x) z)^2 ∂(interpolationLaw F x r T).prod (stdGaussian (Point d)))≤
      (20+16*circuitGrowthConstant^2)*(circuitD F x)^2 := by
  let := interpolationLaw_probability hF x hr (by linarith only [hl]) T
  have hm := interpolationLaw_norm_sq hF x hr hr1 hl hT hT1
  have hg := pairGauge_moment _ hm.1 (circuitD_nonneg F x)
  refine ⟨hg.1,hg.2.trans ?_⟩
  have hs : (1:ℝ)≤Real.sqrt d := by
    exact (by norm_num : (1:ℝ)=Real.sqrt 1).trans_le (Real.sqrt_le_sqrt (by exact_mod_cast hd))
  have hD := hs.trans (sqrt_le_circuitD F x)
  have hd2 := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hd2
  have hs2 := pow_le_pow_left₀ (show 0≤1+circuitD F x by positivity [circuitD_nonneg F x])
    (show 1+circuitD F x≤2*circuitD F x by linarith) 2
  nlinarith [hm.2]

end LogConcaveSampling

end

end

end OAI

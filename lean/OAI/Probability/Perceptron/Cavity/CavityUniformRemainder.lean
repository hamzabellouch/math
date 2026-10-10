import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityTaylorFinite

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def cavityRemainderCoefficients (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (L D : ℝ) : Fin 4→ℝ := ![
  (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*D^2/2+
    (D^2+D*L/2)*‖weightedDerivative g.d1 h1 1‖,
  ‖weightedDerivative g.d2 h2 1‖*D*Real.sqrt D+Real.sqrt D*L*‖g.d1‖,
  ‖weightedDerivative g.d3 h3 1‖*D^2/2+D*L*‖g.d2‖/2,
  ‖g.d3‖*(Real.sqrt D)^3/6]

def cavityRemainderMajorant (c : Fin 4→ℝ) (N u : ℝ) : ℝ :=
  c 0/N^2+c 1*u/(N*Real.sqrt N)+c 2*u^2/N^2+c 3*u^3/(N*Real.sqrt N)

lemma cavityRemainderMajorant_nonneg (c : Fin 4→ℝ) (hc : ∀ i,0≤c i)
    {N u : ℝ} (hN : 0≤N) (hu : 0≤u) : 0≤cavityRemainderMajorant c N u := by
  have h0:=hc 0
  have h1:=hc 1
  have h2:=hc 2
  have h3:=hc 3
  unfold cavityRemainderMajorant
  positivity

lemma cavityRemainderCoefficients_nonneg (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {L D : ℝ} (hL : 0≤L) (hD : 0≤D) :
    ∀ i,0≤cavityRemainderCoefficients g h1 h2 h3 L D i := by
  intro i
  fin_cases i <;> dsimp [cavityRemainderCoefficients] <;> positivity

lemma cavityTaylorError_le_majorant (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {N L D q v u : ℝ}
    (hN : 0<N) (hL : 0≤L) (hD : 0≤D) (hDN : 2*D≤N)
    (hq : 0≤q) (hqD : q≤D) (hu : 0≤u) (hv : |v|≤Real.sqrt D*u) :
    cavityTaylorError g h1 h2 h3 N L q v≤
      cavityRemainderMajorant (cavityRemainderCoefficients g h1 h2 h3 L D) N u := by
  have hsN:=Real.sqrt_pos.mpr hN
  have hsNL : 0<Real.sqrt (N+L) := Real.sqrt_pos.mpr (by linarith)
  have hs : Real.sqrt N≤Real.sqrt (N+L) := Real.sqrt_le_sqrt (by linarith)
  have hlog:=cavity_scale_log_bounds hN hL hD hDN hq hqD
  have hshift:=cavity_shift_difference (v:=v) hN hL
  have hsq:=cavity_square_shift_difference (v:=v) hN hL
  have hv2 : v^2≤D*u^2 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg v) hv 2
    simpa only [sq_abs,mul_pow,Real.sq_sqrt hD] using hh
  have hscaled : |v/Real.sqrt (N+L)|≤Real.sqrt D*u/Real.sqrt N := by
    rw [abs_div,abs_of_pos hsNL]
    exact (div_le_div_of_nonneg_right hv hsNL.le).trans
      (div_le_div_of_nonneg_left (by positivity) hsN hs)
  have ht2 : (Real.log (Real.sqrt (1-q/(N+L))))^2≤(D/N)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hlog.1 2
  have hu2 : (v/Real.sqrt (N+L))^2≤D*u^2/N := by
    rw [div_pow,Real.sq_sqrt (by linarith : 0≤N+L)]
    exact (div_le_div_of_nonneg_right hv2 (by linarith)).trans
      (div_le_div_of_nonneg_left (by positivity) hN (by linarith))
  have h1':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht2 (by positivity : 0≤‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖))
    (by norm_num : (0:ℝ)≤2)
  have h2':=mul_le_mul_of_nonneg_left (mul_le_mul hlog.1 hscaled (abs_nonneg _) (by positivity))
    (norm_nonneg (weightedDerivative g.d2 h2 1))
  have h3':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul hlog.1 hu2 (sq_nonneg _) (by positivity))
      (norm_nonneg (weightedDerivative g.d3 h3 1))) (by norm_num : (0:ℝ)≤2)
  have h4':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hscaled 3) (norm_nonneg g.d3))
    (by norm_num : (0:ℝ)≤6)
  have h5':=mul_le_mul_of_nonneg_right hlog.2 (norm_nonneg (weightedDerivative g.d1 h1 1))
  have h6':=mul_le_mul_of_nonneg_right (hshift.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv hL) (by positivity))) (norm_nonneg g.d1)
  have h7':=mul_le_mul_of_nonneg_right (hsq.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv2 hL) (by positivity))) (norm_nonneg g.d2)
  have ht:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1' h2') h3') h4') h5') h6') h7'
  simp only [mul_assoc] at ht
  dsimp only [cavityTaylorError]
  simp only [mul_assoc]
  apply ht.trans_eq
  dsimp [cavityRemainderMajorant,cavityRemainderCoefficients]
  simp only [div_pow]
  rw [show (Real.sqrt N)^3=N*Real.sqrt N by
    rw [pow_succ,Real.sq_sqrt hN.le]]
  field_simp
  ring

lemma cavityTaylorError_inner_le (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {N D : ℝ} (L : ℕ)
    (hN : 0<N) (hD : 0≤D) (hDN : 2*D≤N) (z y : Spin L) (hz : ‖z‖^2≤D) :
    cavityTaylorError g h1 h2 h3 N L (‖z‖^2) (inner ℝ z y)≤
      cavityRemainderMajorant (cavityRemainderCoefficients g h1 h2 h3 L D) N ‖y‖ := by
  apply cavityTaylorError_le_majorant g h1 h2 h3 hN (Nat.cast_nonneg _) hD hDN
    (sq_nonneg _) hz (norm_nonneg _)
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((Real.le_sqrt (norm_nonneg _) hD).mpr hz) (norm_nonneg _))


def cavityNormMoment (L p : ℕ) : ℝ := ∫ y : Spin L,‖y‖^p ∂stdGaussian (Spin L)

lemma cavityNormMoment_integrable (L p : ℕ) :
    Integrable (fun y : Spin L=>‖y‖^p) (stdGaussian (Spin L)) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (Spin L)) (p:ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma cavityRemainderMajorant_integrable (L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    Integrable (fun y : Spin L=>cavityRemainderMajorant c N ‖y‖) (stdGaussian (Spin L)) := by
  have h1 : Integrable (fun y : Spin L=>‖y‖) (stdGaussian (Spin L)) := by
    simpa using cavityNormMoment_integrable L 1
  exact (((integrable_const (c 0/N^2)).add ((h1.const_mul (c 1)).div_const _)).add
    (((cavityNormMoment_integrable L 2).const_mul (c 2)).div_const _)).add
    (((cavityNormMoment_integrable L 3).const_mul (c 3)).div_const _)

lemma cavityRemainderMajorant_mean (L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    (∫ y : Spin L,cavityRemainderMajorant c N ‖y‖ ∂stdGaussian (Spin L))=
      c 0/N^2+c 1*cavityNormMoment L 1/(N*Real.sqrt N)+
        c 2*cavityNormMoment L 2/N^2+c 3*cavityNormMoment L 3/(N*Real.sqrt N) := by
  have h1 : Integrable (fun y : Spin L=>‖y‖) (stdGaussian (Spin L)) := by
    simpa using cavityNormMoment_integrable L 1
  have h2:=cavityNormMoment_integrable L 2
  have h3:=cavityNormMoment_integrable L 3
  unfold cavityRemainderMajorant cavityNormMoment
  have hi0 : Integrable (fun _ : Spin L=>c 0/N^2) (stdGaussian (Spin L)) := integrable_const _
  have hi1 : Integrable (fun y : Spin L=>c 1*‖y‖/(N*Real.sqrt N)) (stdGaussian (Spin L)) :=
    (h1.const_mul _).div_const _
  have hi2 : Integrable (fun y : Spin L=>c 2*‖y‖^2/N^2) (stdGaussian (Spin L)) :=
    (h2.const_mul _).div_const _
  have hi3 : Integrable (fun y : Spin L=>c 3*‖y‖^3/(N*Real.sqrt N)) (stdGaussian (Spin L)) :=
    (h3.const_mul _).div_const _
  have ha := integral_add ((hi0.add hi1).add hi2) hi3
  have hb := integral_add (hi0.add hi1) hi2
  have hd := integral_add hi0 hi1
  simp only [Pi.add_apply] at ha hb hd
  rw [ha,hb,hd]
  simp only [integral_div,integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,pow_one]

lemma cavityRemainderMajorant_row_mean (M L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    (∫ y : Fin M→Spin L,∑ i,cavityRemainderMajorant c N ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
    M*(c 0/N^2+c 1*cavityNormMoment L 1/(N*Real.sqrt N)+
        c 2*cavityNormMoment L 2/N^2+c 3*cavityNormMoment L 3/(N*Real.sqrt N)) := by
  have hi (i : Fin M) : Integrable
      (fun y : Fin M→Spin L=>cavityRemainderMajorant c N ‖y i‖)
      (Measure.pi (fun _=>stdGaussian (Spin L))) :=
    ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i).integrable_comp
      (cavityRemainderMajorant_integrable L c N).aestronglyMeasurable).mpr
      (cavityRemainderMajorant_integrable L c N)
  rw [integral_finsetSum _ (fun i _=>hi i)]
  have he (i : Fin M) :
      (∫ y : Fin M→Spin L,cavityRemainderMajorant c N ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin L))) =
      ∫ y : Spin L,cavityRemainderMajorant c N ‖y‖ ∂stdGaussian (Spin L) := by
    have hp := measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i
    have hh := (integral_map hp.measurable.aemeasurable
      (hp.map_eq ▸ (cavityRemainderMajorant_integrable L c N).aestronglyMeasurable)).symm
    simpa only [hp.map_eq,Function.eval] using hh
  simp_rw [he,cavityRemainderMajorant_mean]
  simp
  ring

lemma cavityRemainderMajorant_row_tendsto (M : ℕ→ℕ) (L : ℕ) (c : Fin 4→ℝ)
    {α : ℝ} (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>∫ y : Fin (M n)→Spin L,∑ i,cavityRemainderMajorant c (n+1:ℕ) ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin L))) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hs : Tendsto (fun n : ℕ=>(Real.sqrt (n+1:ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have ht:=hM.mul (((hi.const_mul (c 0)).add (hs.const_mul (c 1*cavityNormMoment L 1))).add
    (hi.const_mul (c 2*cavityNormMoment L 2)) |>.add (hs.const_mul (c 3*cavityNormMoment L 3)))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [cavityRemainderMajorant_row_mean]
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI

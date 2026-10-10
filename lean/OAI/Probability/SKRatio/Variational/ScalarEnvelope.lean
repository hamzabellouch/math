import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarTemperature

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def endpointK (y : ℝ) : ℝ :=
  (1/16)*(∫ h, (1-y^2+v h)^2/multiplier h ∂fieldLaw (1/2))
def endpointD (y : ℝ) : ℝ :=
  (1/4)*(∫ h, v h^2/(2-y-m h) ∂fieldLaw (1/2))
def endpointDPrime : ℝ :=
  (1/4)*(∫ h, v h^2/(2-m h)^2 ∂fieldLaw (1/2))

lemma integrable_K_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {y : ℝ} (hy : |y| ≤ 1) :
    Integrable (fun h => (1-y^2+v h)^2/multiplier h) μ := by
  have hy2 : y^2 ≤ 1 := by simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)).mpr hy
  apply (integrable_const (12:ℝ)).mono'
    (((continuous_const.add continuous_v).pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |(1-y^2+v h)^2/multiplier h| ≤ 12
  have hs : (1-y^2+v h)^2 ≤ 4 := by nlinarith [sq_nonneg y,v_le_one h,(v_pos h).le]
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (multiplier_strict_pos h).le)]
  exact (div_le_div_of_nonneg_right hs (multiplier_strict_pos h).le).trans (by
    rw [div_le_iff₀ (multiplier_strict_pos h)]
    linarith [multiplier_pos h])

lemma D_integrand_pos {y : ℝ} (hy : y ≤ 1) (h : ℝ) : 0 < 2-y-m h := by
  linarith [(m_bounds h).2]

lemma D_integrand_le_two {y : ℝ} (hy : y ≤ 1) (h : ℝ) :
    |v h^2/(2-y-m h)| ≤ 2 := by
  have hd := D_integrand_pos hy h
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
  apply (div_le_iff₀ hd).mpr
  have hbase : v h^2 ≤ 2*(1-m h) := by
    have hvw : v h = (1-m h)*(1+m h) := by unfold v; ring
    have hv : v h^2 ≤ v h := by nlinarith [v_le_one h,(v_pos h).le]
    have hmu := (m_bounds h).2
    have hmm : v h ≤ 2*(1-m h) := by rw [hvw]; nlinarith [sq_nonneg (1-m h)]
    linarith
  linarith

lemma integrable_D_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {y : ℝ} (hy : y ≤ 1) : Integrable (fun h => v h^2/(2-y-m h)) μ := by
  exact (integrable_const (2:ℝ)).mono'
    ((continuous_v.pow 2).div (continuous_const.sub continuous_m)
      (fun h => (D_integrand_pos hy h).ne')).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using D_integrand_le_two hy h))

lemma integrable_DPrime_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Integrable (fun h => v h^2/(2-m h)^2) μ := by
  have hden (h : ℝ) : 0 < 2-m h := by linarith [(m_bounds h).2]
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_v.pow 2).div ((continuous_const.sub continuous_m).pow 2)
      (fun h => pow_ne_zero _ (hden h).ne')).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |v h^2/(2-m h)^2| ≤ 1
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (div_le_one (sq_pos_of_pos (hden h))).mpr
  nlinarith [v_le_one h,(v_pos h).le,(m_bounds h).2]

lemma endpointK_quadratic {y : ℝ} (hy : |y| ≤ 1) :
    endpointK y ≤ endpointK 0+(endpointK 1-endpointK 0)*y^2 := by
  have hy2 : y^2 ≤ 1 := by simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)).mpr hy
  have hi0 : Integrable (fun h => (1+v h)^2/multiplier h) (fieldLaw (1/2)) := by
    simpa using integrable_K_integrand (y := 0) (μ := fieldLaw (1/2)) (by norm_num)
  have hi1 : Integrable (fun h => v h^2/multiplier h) (fieldLaw (1/2)) := by
    simpa using integrable_K_integrand (y := 1) (μ := fieldLaw (1/2)) (by norm_num)
  have hp (h : ℝ) : (1-y^2+v h)^2/multiplier h ≤
      (1-y^2)*((1+v h)^2/multiplier h)+y^2*(v h^2/multiplier h) := by
    have hs : (1-y^2+v h)^2 ≤ (1-y^2)*(1+v h)^2+y^2*v h^2 := by
      nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy2)]
    convert! div_le_div_of_nonneg_right hs (multiplier_strict_pos h).le using 1
    ring
  have hi := integral_mono (integrable_K_integrand hy)
    ((hi0.const_mul (1-y^2)).add (hi1.const_mul (y^2))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hi0.const_mul _) (hi1.const_mul _),integral_const_mul,integral_const_mul] at hi
  dsimp [endpointK]
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero,one_pow,sub_self,zero_add]
  nlinarith only [hi]

lemma resolvent_quadratic {A y : ℝ} (hA : 1 < A) (hy : y ≤ 1) :
    1/(A-y) ≤ 1/A+y/A^2+y^2*(1/(A-1)-1/A-1/A^2) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A-1 := by linarith
  have hAy : 0 < A-y := by linarith
  have he : (1/A+y/A^2+y^2*(1/(A-1)-1/A-1/A^2))-1/(A-y) =
      y^2*(1-y)/(A^2*(A-1)*(A-y)) := by
    field_simp
    ring
  have hz : 0 ≤ y^2*(1-y)/(A^2*(A-1)*(A-y)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hy)) (by positivity)
  linarith only [he,hz]

lemma endpointD_quadratic {y : ℝ} (hy : y ≤ 1) :
    endpointD y ≤ endpointD 0+endpointDPrime*y+
      y^2*(endpointD 1-endpointD 0-endpointDPrime) := by
  let b0 := fun h => v h^2/(2-m h)
  let b1 := fun h => v h^2/(1-m h)
  let bp := fun h => v h^2/(2-m h)^2
  have hi0 : Integrable b0 (fieldLaw (1/2)) := by
    simpa only [sub_zero,b0] using integrable_D_integrand (y := 0) (μ := fieldLaw (1/2)) (by norm_num)
  have hi1 : Integrable b1 (fieldLaw (1/2)) := by
    simpa only [b1,show (2:ℝ)-1=1 from by norm_num] using
      integrable_D_integrand (y := 1) (μ := fieldLaw (1/2)) (by norm_num)
  have hip : Integrable bp (fieldLaw (1/2)) := integrable_DPrime_integrand
  have hrem : Integrable (fun h => b1 h-b0 h-bp h) (fieldLaw (1/2)) :=
    (hi1.sub hi0).sub hip
  have ihl : Integrable (fun h => b0 h+y*bp h) (fieldLaw (1/2)) := hi0.add (hip.const_mul _)
  have hp (h : ℝ) : v h^2/(2-y-m h) ≤ b0 h+y*bp h+y^2*(b1 h-b0 h-bp h) := by
    have hh := mul_le_mul_of_nonneg_left (resolvent_quadratic (A := 2-m h) (by
      linarith [(m_bounds h).2]) hy) (sq_nonneg (v h))
    convert! hh using 1
    · have hd : (2:ℝ)-m h-y = 2-y-m h := by ring
      rw [hd]; ring
    · dsimp [b0,b1,bp]
      have hd : (2:ℝ)-m h-1 = 1-m h := by ring
      rw [hd]; ring
  have hi := integral_mono (integrable_D_integrand hy) (ihl.add (hrem.const_mul _)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add ihl (hrem.const_mul _),integral_add hi0 (hip.const_mul _),
    integral_const_mul,integral_const_mul] at hi
  have hir : (∫ h, b1 h-b0 h-bp h ∂fieldLaw (1/2)) =
      (∫ h, b1 h ∂fieldLaw (1/2))-(∫ h, b0 h ∂fieldLaw (1/2))-(∫ h, bp h ∂fieldLaw (1/2)) := by
    have hsub : Integrable (fun h => b1 h-b0 h) (fieldLaw (1/2)) := hi1.sub hi0
    rw [integral_sub hsub hip,integral_sub hi1 hi0]
  rw [hir] at hi
  dsimp [endpointD,endpointDPrime]
  simp only [sub_zero,show (2:ℝ)-1=1 from by norm_num]
  dsimp [b0,b1,bp] at hi
  nlinarith only [hi]

lemma endpointD_field (h : ℝ) : diagonal (fieldLaw (1/2)) (1/2) h = endpointD (m h) := by
  unfold diagonal endpointD w
  have hd (t : ℝ) : 1-m h+(1-m t) = 2-m h-m t := by ring
  simp_rw [hd]
  congr 1
  norm_num

lemma endpointK_field (h : ℝ) : cost (fieldLaw (1/2)) (1/2) h = endpointK (m h) := by
  unfold cost endpointK
  norm_num only [show (1/2:ℝ)^2/4 = 1/16 by norm_num]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  rw [v]
  change (1/16)*(v t+(1-m h^2))^2/multiplier t = (1/16)*((1-m h^2+v t)^2/multiplier t)
  ring

lemma envelope_of_endpoint_data
    (hk0 : endpointK 0 ≤ 4280/10000) (hk1 : endpointK 1 ≤ 902/10000)
    (hd0 : endpointD 0 ≤ 929/10000) (hd1 : endpointD 1 ≤ 2292/10000)
    (hdp0 : 520/10000 ≤ endpointDPrime) (hdp1 : endpointDPrime ≤ 526/10000)
    {β : ℝ} (hβ : 0 < β) (hβh : β ≤ 1/2) (h : ℝ) :
    multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ 9789/10000 := by
  have hm := m_bounds h
  have hma : |m h| ≤ 1 := (abs_lt.mpr hm).le
  have hy2 : m h^2 ≤ 1 := (tanh_sq_lt_one h).le
  have hD := diagonal_temperature_mono hβ hβh (by norm_num : (1/2:ℝ) ≤ 1) h
  have hK := cost_temperature_mono hβ hβh (by norm_num : (1/2:ℝ) ≤ 1) h
  rw [endpointD_field] at hD
  rw [endpointK_field] at hK
  have hDQ := endpointD_quadratic hm.2.le
  have hKQ := endpointK_quadratic hma
  have hA : 45/100+endpointD 0+endpointK 0 ≤ (9709/10000:ℝ) := by linarith
  have hB : 70/100+endpointK 1+endpointD 1-endpointDPrime ≤ (9709/10000:ℝ) := by linarith
  have hM : |endpointDPrime-6/100| ≤ (80/10000:ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hC : (endpointDPrime-6/100)*m h ≤ (80/10000:ℝ) := by
    calc
      _ ≤ |endpointDPrime-6/100| *|m h| := by rw [←abs_mul]; exact le_abs_self _
      _ ≤ 80/10000 := by nlinarith [mul_le_mul hM hma (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 80/10000)]
  have hAw := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hy2)
  have hBw := mul_le_mul_of_nonneg_left hB (sq_nonneg (m h))
  unfold multiplier
  nlinarith only [hD,hK,hDQ,hKQ,hAw,hBw,hC]

end SKRatio.Scalar

end

end OAI

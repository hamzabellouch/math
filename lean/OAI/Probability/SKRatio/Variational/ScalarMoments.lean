import Mathlib
import OAI.Probability.SKRatio.Matrices.StandardGaussianProduct
import OAI.Probability.SKRatio.Gaussian.Planted
import OAI.Probability.SKRatio.Variational.ScalarKernel

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def variance (β : ℝ) : ℝ≥0 := Real.toNNReal (β^2)

@[simp] lemma variance_coe (β : ℝ) : (variance β : ℝ) = β^2 :=
  Real.coe_toNNReal _ (sq_nonneg β)

def fieldLaw (β : ℝ) : Measure ℝ := gaussianReal (β^2) (variance β)
instance (β : ℝ) : IsProbabilityMeasure (fieldLaw β) := by
  unfold fieldLaw
  infer_instance

lemma memLp_m {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp m p μ := by
  apply MemLp.of_bound continuous_m.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using (abs_lt.mpr (m_bounds h)).le)

lemma memLp_v {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp v p μ := by
  apply MemLp.of_bound continuous_v.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs,abs_of_nonneg (v_pos h).le] using v_le_one h)

lemma memLp_mv {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} :
    MemLp (fun h => m h*v h) p μ := by
  apply MemLp.of_bound (continuous_m.mul continuous_v).aestronglyMeasurable 1
  apply ae_of_all
  intro h
  change |m h*v h| ≤ 1
  rw [abs_mul,abs_of_nonneg (v_pos h).le]
  exact (mul_le_mul (abs_lt.mpr (m_bounds h)).le (v_le_one h)
    (v_pos h).le (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)

lemma tilted_integral (β : ℝ) (f : ℝ → ℝ) :
    ∫ h, f h ∂fieldLaw β =
      ∫ h, exp (h-β^2/2)*f h ∂gaussianReal 0 (variance β) := by
  have he := Planted.gaussianReal_tilt 0 (variance β) 1
  simp only [one_mul,mul_zero,one_pow,mul_one,zero_add,variance_coe] at he
  rw [fieldLaw,←he,integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun h => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul]

lemma centered_gaussian_integral_neg (s : ℝ≥0) (f : ℝ → ℝ) :
    ∫ h, f (-h) ∂gaussianReal 0 s = ∫ h, f h ∂gaussianReal 0 s := by
  have hp : MeasurePreserving (fun h : ℝ => -h) (gaussianReal 0 s) (gaussianReal 0 s) :=
    ⟨measurable_neg,by simpa using (gaussianReal_map_neg (μ := 0) (v := s))⟩
  exact hp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding f

lemma tilted_odd_integrand (h : ℝ) :
    exp h*(m h-m h^2) = -(exp (-h)*(m (-h)-m (-h)^2)) := by
  have hh := Calculus.exp_two_mul_one_sub_tanh h
  have hp := exp_pos h
  simp only [show 2*h=h+h by ring,exp_add,m,tanh_neg,neg_sq] at hh ⊢
  rw [exp_neg]
  field_simp
  nlinarith only [hh, mul_eq_mul_right_iff.mp (congrArg (fun t : ℝ => t*tanh h) hh)]

theorem sign_identity (β : ℝ) (F : ℝ → ℝ) (hF : Measurable F)
    (heven : ∀ h, F (-h) = F h) {C : ℝ} (hC : ∀ h, |F h| ≤ C) :
    ∫ h, m h*F h ∂fieldLaw β = ∫ h, m h^2*F h ∂fieldLaw β := by
  have hFlp : MemLp F 2 (fieldLaw β) := MemLp.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using hC h))
  have h1 : Integrable (fun h => m h*F h) (fieldLaw β) := (memLp_m (p := 2)).integrable_mul hFlp
  have hm2 : MemLp (fun h => m h^2) 2 (fieldLaw β) := by
    apply MemLp.of_bound (continuous_m.pow 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun h => by
      change |m h^2| ≤ 1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (tanh_sq_lt_one h).le)
  have h2 : Integrable (fun h => m h^2*F h) (fieldLaw β) := hm2.integrable_mul hFlp
  suffices hz : ∫ h, m h*F h-m h^2*F h ∂fieldLaw β = 0 by
    rw [integral_sub h1 h2] at hz
    linarith
  rw [tilted_integral]
  let A : ℝ → ℝ := fun h => exp (h-β^2/2)*(m h*F h-m h^2*F h)
  have ha (h : ℝ) : A (-h) = -A h := by
    have hh := tilted_odd_integrand h
    dsimp [A]
    rw [heven h,exp_sub,exp_sub]
    have hd := (exp_pos (β^2/2)).ne'
    apply (mul_right_cancel₀ hd)
    field_simp
    have hhh := congrArg (fun t : ℝ => t*F h) hh
    nlinarith only [hhh]
  have hi := centered_gaussian_integral_neg (variance β) A
  simp_rw [ha,integral_neg] at hi
  change ∫ h, A h ∂gaussianReal 0 (variance β) = 0
  linarith

lemma mean_m_eq_mean_m_sq (β : ℝ) :
    ∫ h, m h ∂fieldLaw β = ∫ h, m h^2 ∂fieldLaw β := by
  simpa using sign_identity β (fun _ => (1:ℝ)) measurable_const (fun _ => rfl)
    (C := 1) (fun _ => by norm_num)

lemma mean_mv_eq_mean_m_sq_v (β : ℝ) :
    ∫ h, m h*v h ∂fieldLaw β = ∫ h, m h^2*v h ∂fieldLaw β := by
  apply sign_identity β v continuous_v.measurable
  · intro h
    simp [v,m,tanh_neg]
  · intro h
    simpa only [abs_of_nonneg (v_pos h).le] using v_le_one h

lemma mean_mv_nonneg (β : ℝ) : 0 ≤ ∫ h, m h*v h ∂fieldLaw β := by
  rw [mean_mv_eq_mean_m_sq_v]
  exact integral_nonneg (fun h => mul_nonneg (sq_nonneg _) (v_pos h).le)

lemma memLp_field (β : ℝ) : MemLp (fun h : ℝ => h) 2 (fieldLaw β) :=
  memLp_id_gaussianReal 2

lemma memLp_field_v (β : ℝ) : MemLp (fun h : ℝ => h*v h) 2 (fieldLaw β) := by
  apply (memLp_field β).of_le_mul
    (continuous_id.mul continuous_v).aestronglyMeasurable (c := (1:ℝ))
  apply ae_of_all
  intro h
  change |h*v h| ≤ 1*|h|
  simp only [abs_mul,one_mul,abs_of_nonneg (v_pos h).le]
  exact mul_le_of_le_one_right (abs_nonneg _) (v_le_one h)

lemma v_hasDerivAt (h : ℝ) : HasDerivAt v (-2*m h*v h) h := by
  convert! (hasDerivAt_const h (1:ℝ)).sub ((Calculus.hasDerivAt_tanh h).pow 2) using 1
  simp only [v,m,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
  ring

theorem field_variance_identity (β : ℝ) :
    ∫ h, (h-β^2+2*β^2*m h)*v h ∂fieldLaw β = 0 := by
  by_cases hβ : β = 0
  · subst β
    have he : fieldLaw 0 = Measure.dirac 0 := by
      unfold fieldLaw
      norm_num [variance]
    rw [he]
    simp [m,v]
  have hs : ((variance β) : ℝ≥0) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact hβ (by simpa only [variance_coe,NNReal.coe_zero,pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)] using hh)
  have hvI : Integrable v (fieldLaw β) := memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hmvI : Integrable (fun h => m h*v h) (fieldLaw β) :=
    memLp_mv.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hhvI : Integrable (fun h => h*v h) (fieldLaw β) :=
    (memLp_field_v β).integrable (by norm_num)
  have hvder : Integrable (fun h => -2*m h*v h) (fieldLaw β) := by
    simpa only [mul_assoc] using hmvI.const_mul (-2:ℝ)
  have hcenter : Integrable (fun h => (h-β^2)*v h) (fieldLaw β) := by
    convert! hhvI.sub (hvI.const_mul (β^2)) using 1
    ext h
    dsimp
    ring
  have hh := SKRatioGaussian.gaussian_integration_by_parts hs v_hasDerivAt hvI hvder hcenter
  have hexp (h : ℝ) : (h-β^2+2*β^2*m h)*v h = (h-β^2)*v h+(2*β^2)*(m h*v h) := by ring
  simp_rw [hexp]
  rw [integral_add hcenter (hmvI.const_mul _),integral_const_mul]
  have hsimp : (∫ h, (h-β^2)*v h ∂fieldLaw β) =
      β^2*((-2)*(∫ h, m h*v h ∂fieldLaw β)) := by
    simpa only [fieldLaw,variance_coe,mul_assoc,integral_const_mul] using hh
  rw [hsimp]
  ring

def multiplier (h : ℝ) : ℝ := 45/100 + (1/4)*m h^2 - (6/100)*m h

lemma multiplier_pos (h : ℝ) : 4464/10000 ≤ multiplier h := by
  unfold multiplier
  nlinarith [sq_nonneg (m h-12/100)]

lemma multiplier_le (h : ℝ) : multiplier h ≤ 76/100 := by
  unfold multiplier
  have hm := m_bounds h
  have hs := (tanh_sq_lt_one h).le
  change m h^2 ≤ 1 at hs
  nlinarith

lemma continuous_multiplier : Continuous multiplier := by
  exact (continuous_const.add ((continuous_m.pow 2).const_mul (1/4))).sub
    (continuous_m.const_mul (6/100))

lemma mean_multiplier (β : ℝ) :
    ∫ h, multiplier h ∂fieldLaw β = 64/100-(19/100)*(∫ h, v h ∂fieldLaw β) := by
  have hmI : Integrable m (fieldLaw β) := memLp_m.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hm2I : Integrable (fun h => m h^2) (fieldLaw β) := memLp_m.integrable_sq
  have hv : (∫ h, v h ∂fieldLaw β) = 1-∫ h, m h^2 ∂fieldLaw β := by
    unfold v
    rw [integral_sub (integrable_const 1) hm2I,integral_const]
    simp
  have hsum : Integrable (fun h => 45/100+(1/4)*m h^2) (fieldLaw β) := by
    exact (integrable_const (45/100:ℝ)).add (hm2I.const_mul (1/4:ℝ))
  unfold multiplier
  rw [integral_sub hsum (hmI.const_mul _),
    integral_add (integrable_const _) (hm2I.const_mul _),integral_const_mul,integral_const_mul,
    integral_const,mean_m_eq_mean_m_sq,hv]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

end SKRatio.Scalar

end
end

end OAI

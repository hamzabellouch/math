import Mathlib
import OAI.Probability.SKGap.Localization.LiteralRegularity

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal
variable {n : ℕ}

def channelReference (n : ℕ) : Measure (Fin n→ℝ) := Measure.pi (fun _=>gaussianReal 0 1)
instance channelReference_probability (n : ℕ) : IsProbabilityMeasure (channelReference n) := by
  unfold channelReference
  infer_instance

def gaussianChannelLikelihood (T : ℝ) (x : Spin n) (z : Fin n→ℝ) : ℝ :=
  exp ((∑ i,sqrt T*spinValue (x i)*z i)-(n:ℝ)*T/2)

def gaussianChannelDensity (g : Disorder n) (T : ℝ) (z : Fin n→ℝ) : ℝ :=
  ∑ x,mass g 0 x*gaussianChannelLikelihood T x z

def gaussianChannelLaw (g : Disorder n) (T : ℝ) : Measure (Fin n→ℝ) :=
  (channelReference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelDensity g T z))

lemma channel_linear_exp_integrable (a : Fin n→ℝ) :
    Integrable (fun z : Fin n→ℝ=>exp (∑ i,a i*z i)) (channelReference n) := by
  simp only [exp_sum,channelReference]
  exact Integrable.fintype_prod (fun i=>integrable_exp_mul_gaussianReal (a i))

lemma channel_linear_exp_integral (a : Fin n→ℝ) :
    (∫ z,exp (∑ i,a i*z i) ∂channelReference n)=exp ((∑ i,a i^2)/2) := by
  simp only [exp_sum,channelReference]
  rw [integral_fintype_prod_eq_prod (fun i z=>exp (a i*z))]
  have he (i : Fin n) : (∫ z : ℝ,exp (a i*z) ∂gaussianReal 0 1)=exp (a i^2/2) := by
    change mgf id (gaussianReal 0 1) (a i)=_
    rw [mgf_id_gaussianReal]
    simp
  simp only [he,← exp_sum,Finset.sum_div]

lemma gaussianChannelLikelihood_integrable (T : ℝ) (x : Spin n) :
    Integrable (gaussianChannelLikelihood T x) (channelReference n) := by
  have he : gaussianChannelLikelihood T x=fun z=>exp (∑ i,sqrt T*spinValue (x i)*z i)*exp (-(n:ℝ)*T/2) := by
    funext z
    rw [gaussianChannelLikelihood,← exp_add]
    congr 1;ring
  rw [he]
  exact (channel_linear_exp_integrable (fun i=>sqrt T*spinValue (x i))).mul_const _

lemma gaussianChannelLikelihood_integral {T : ℝ} (hT : 0 ≤ T) (x : Spin n) :
    (∫ z,gaussianChannelLikelihood T x z ∂channelReference n)=1 := by
  have he : gaussianChannelLikelihood T x=fun z=>exp (∑ i,sqrt T*spinValue (x i)*z i)*exp (-(n:ℝ)*T/2) := by
    funext z
    rw [gaussianChannelLikelihood,← exp_add]
    congr 1;ring
  rw [he,integral_mul_const,channel_linear_exp_integral,← exp_add]
  simp only [mul_pow,sq_sqrt hT,spinValue_sq,mul_one,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  convert exp_zero using 1
  congr 1;ring

lemma gaussianChannelDensity_pos (g : Disorder n) (T : ℝ) (z : Fin n→ℝ) :
    0 < gaussianChannelDensity g T z :=
  Finset.sum_pos (fun x _=>mul_pos (mass_pos g 0 x) (exp_pos _)) Finset.univ_nonempty

lemma gaussianChannelDensity_continuous (g : Disorder n) (T : ℝ) :
    Continuous (gaussianChannelDensity g T) := by
  unfold gaussianChannelDensity gaussianChannelLikelihood
  fun_prop

lemma gaussianChannelDensity_integrable (g : Disorder n) (T : ℝ) :
    Integrable (gaussianChannelDensity g T) (channelReference n) :=
  integrable_finsetSum _ (fun x _=>(gaussianChannelLikelihood_integrable T x).const_mul _)

lemma gaussianChannelDensity_integral (g : Disorder n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ z,gaussianChannelDensity g T z ∂channelReference n)=1 := by
  unfold gaussianChannelDensity
  rw [integral_finsetSum _ (fun x _=>(gaussianChannelLikelihood_integrable T x).const_mul _)]
  simp only [integral_const_mul,gaussianChannelLikelihood_integral hT,mul_one,sum_mass]

lemma gaussianChannelLaw_probability (g : Disorder n) {T : ℝ} (hT : 0 ≤ T) :
    IsProbabilityMeasure (gaussianChannelLaw g T) := by
  constructor
  rw [gaussianChannelLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gaussianChannelDensity_integrable g T)
      (ae_of_all _ (fun z=>(gaussianChannelDensity_pos g T z).le)),gaussianChannelDensity_integral g hT]
  exact ENNReal.ofReal_one

lemma weight_field_shift (g : Disorder n) (h : Fin n→ℝ) (x : Spin n) :
    weight g h x=weight g 0 x*exp (∑ i,h i*spinValue (x i)) := by
  unfold weight hamiltonian
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,exp_add]

lemma gaussianChannelDensity_partition (g : Disorder n) (T : ℝ) (z : Fin n→ℝ) :
    gaussianChannelDensity g T z=exp (-(n:ℝ)*T/2)*partition g (fun i=>sqrt T*z i)/partition g 0 := by
  unfold gaussianChannelDensity gaussianChannelLikelihood
  have he (x : Spin n) : mass g 0 x*exp ((∑ i,sqrt T*spinValue (x i)*z i)-(n:ℝ)*T/2)=
      exp (-(n:ℝ)*T/2)*weight g (fun i=>sqrt T*z i) x/partition g 0 := by
    rw [weight_field_shift]
    have hs : (∑ i,sqrt T*spinValue (x i)*z i)=(∑ i,sqrt T*z i*spinValue (x i)) :=
      Finset.sum_congr rfl (fun i _=>by ring)
    rw [hs,sub_eq_add_neg,exp_add]
    unfold mass
    have hn : -((n:ℝ)*T/2)=-(n:ℝ)*T/2 := by ring
    rw [hn]
    ring
  simp_rw [he]
  rw [← Finset.sum_div,← Finset.mul_sum]
  rfl

lemma gaussianChannel_posterior_identity (g : Disorder n) (T : ℝ) (z : Fin n→ℝ) (x : Spin n) :
    gaussianChannelDensity g T z*mass g (fun i=>sqrt T*z i) x=
      mass g 0 x*gaussianChannelLikelihood T x z := by
  rw [gaussianChannelDensity_partition]
  have he := weight_field_shift g (fun i=>sqrt T*z i) x
  have hs : (∑ i,sqrt T*spinValue (x i)*z i)=(∑ i,sqrt T*z i*spinValue (x i)) :=
      Finset.sum_congr rfl (fun i _=>by ring)
  unfold mass gaussianChannelLikelihood
  rw [hs,sub_eq_add_neg,exp_add,he]
  have hn : -((n:ℝ)*T/2)=-(n:ℝ)*T/2 := by ring
  rw [hn]
  field_simp [(partition_pos g 0).ne',(partition_pos g (fun i=>sqrt T*z i)).ne']

lemma gaussianChannel_mass_mean (g : Disorder n) {T : ℝ} (hT : 0 ≤ T) (x : Spin n) :
    (∫ z,mass g (fun i=>sqrt T*z i) x ∂gaussianChannelLaw g T)=mass g 0 x := by
  rw [gaussianChannelLaw,integral_withDensity_eq_integral_toReal_smul
    (gaussianChannelDensity_continuous g T).measurable.ennreal_ofReal
    (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianChannelDensity_pos g T _).le,smul_eq_mul,
    gaussianChannel_posterior_identity]
  rw [integral_const_mul,gaussianChannelLikelihood_integral hT,mul_one]
end SKGap

end
end

end OAI

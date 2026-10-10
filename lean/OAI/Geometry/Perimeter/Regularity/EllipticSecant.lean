import OAI.Geometry.Perimeter.Regularity.EllipticCurl

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def derivativeSecant (G : Euc n → Euc n) (a b : Euc n) : Euc n →L[ℝ] Euc n :=
  ∫ t in (0:ℝ)..1, fderiv ℝ G (a+t•(b-a))

 theorem derivativeSecant_continuous {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G) :
    Continuous (fun z : Euc n × Euc n ↦ derivativeSecant G z.1 z.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hG.continuous_fderiv (by simp)).comp
    (continuous_fst.fst.add (continuous_snd.smul (continuous_fst.snd.sub continuous_fst.fst)))

 theorem derivativeSecant_apply {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G) (a b : Euc n) :
    derivativeSecant G a b (b-a)=G b-G a := by
  have hc : Continuous (fun t : ℝ ↦ fderiv ℝ G (a+t•(b-a))) :=
    (hG.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))
  rw [derivativeSecant,ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ G (a+s•(b-a)))
      (fderiv ℝ G (a+t•(b-a)) (b-a)) t := by
    apply (hG.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    simpa using ((hasDerivAt_id t).smul_const (b-a) |>.const_add a)
  simpa only [zero_smul,add_zero,one_smul,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      ((hc.clm_apply continuous_const).intervalIntegrable 0 1)

 theorem derivativeSecant_near {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    (a b : Euc n) (A : Euc n →L[ℝ] Euc n) (δ : ℝ)
    (hb : ∀ t∈Icc (0:ℝ) 1, ‖A-fderiv ℝ G (a+t•(b-a))‖≤δ) :
    ‖A-derivativeSecant G a b‖≤δ := by
  have hc : Continuous (fun t : ℝ ↦ fderiv ℝ G (a+t•(b-a))) :=
    (hG.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))
  have he : A-derivativeSecant G a b=∫ t in (0:ℝ)..1, A-fderiv ℝ G (a+t•(b-a)) := by
    let : CompleteSpace (Euc n →L[ℝ] Euc n) := ContinuousLinearMap.instCompleteSpace
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable 0 1)]
    simp only [derivativeSecant, intervalIntegral.integral_const, sub_zero, one_smul]
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht ↦
    hb t (by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at ht
      exact Set.Ioc_subset_Icc_self ht))
  simpa using hh

 theorem derivativeSecant_difference {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    (a b a' b' : Euc n) (C : ℝ)
    (hb : ∀ t∈Icc (0:ℝ) 1,
      ‖fderiv ℝ G (a+t•(b-a))-fderiv ℝ G (a'+t•(b'-a'))‖≤C) :
    ‖derivativeSecant G a b-derivativeSecant G a' b'‖≤C := by
  have hc (a b : Euc n) : Continuous (fun t : ℝ ↦ fderiv ℝ G (a+t•(b-a))) :=
    (hG.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))
  rw [derivativeSecant,derivativeSecant,←intervalIntegral.integral_sub
    ((hc a b).intervalIntegrable 0 1) ((hc a' b').intervalIntegrable 0 1)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht ↦
    hb t (by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at ht
      exact Set.Ioc_subset_Icc_self ht))
  simpa using hh

end RPISingularHarnack

end

end OAI

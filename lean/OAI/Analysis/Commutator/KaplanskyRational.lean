import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

def rationalClip (t : ℝ) : ℝ := 2*t/(1+t^2)

def rationalKernel (t : ℝ) : ℝ := (1+t^2)⁻¹

lemma denom_pos (t : ℝ) : 0<1+t^2 := by positivity

lemma continuous_rationalKernel : Continuous rationalKernel := by
  unfold rationalKernel
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => ne_of_gt (denom_pos t))

lemma continuous_rationalClip : Continuous rationalClip := by
  unfold rationalClip
  exact (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (denom_pos t))

lemma rationalKernel_bound (t : ℝ) : ‖rationalKernel t‖≤1 := by
  rw [rationalKernel,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos t))]
  exact (inv_le_one₀ (denom_pos t)).mpr (by nlinarith [sq_nonneg t])

lemma rationalClip_bound (t : ℝ) : ‖rationalClip t‖≤1 := by
  rw [rationalClip,Real.norm_eq_abs,abs_div,abs_of_pos (denom_pos t)]
  apply (div_le_one (denom_pos t)).mpr
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [sq_nonneg (|t|-1),sq_abs t]

def rationalLift (t : ℝ) : ℝ := t/(1+Real.sqrt (1-t^2))

lemma lift_denom_pos (t : ℝ) : 0<1+Real.sqrt (1-t^2) := by positivity

lemma continuous_rationalLift : Continuous rationalLift := by
  unfold rationalLift
  exact continuous_id.div
    (continuous_const.add ((continuous_const.sub (continuous_id.pow 2)).sqrt))
    (fun t => ne_of_gt (lift_denom_pos t))

lemma rationalClip_lift {t : ℝ} (ht : |t|≤1) :
    rationalClip (rationalLift t)=t := by
  have ht2 : 0≤1-t^2 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have hs := Real.sq_sqrt ht2
  have hd := ne_of_gt (lift_denom_pos t)
  unfold rationalClip rationalLift
  apply (div_eq_iff (ne_of_gt (denom_pos _))).mpr
  field_simp
  have he : (1+Real.sqrt (1-t^2))^2+t^2=2*(1+Real.sqrt (1-t^2)) := by nlinarith
  rw [he]
  ring

variable {A : Type*} [CStarAlgebra A]

def kernel (a : A) : A := cfc rationalKernel a

def clip (a : A) : A := cfc rationalClip a

lemma kernel_norm_le (a : A) : ‖kernel a‖≤1 :=
  norm_cfc_le (by norm_num) (fun t _ => rationalKernel_bound t)

lemma clip_norm_le (a : A) : ‖clip a‖≤1 :=
  norm_cfc_le (by norm_num) (fun t _ => rationalClip_bound t)

lemma clip_selfAdjoint (a : A) : IsSelfAdjoint (clip a) := cfc_predicate _ _

lemma kernel_selfAdjoint (a : A) : IsSelfAdjoint (kernel a) := cfc_predicate _ _

lemma clip_formula {a : A} (ha : IsSelfAdjoint a) :
    clip a=(2:ℝ) • (a*kernel a) := by
  unfold clip rationalClip kernel
  have he : (fun t : ℝ => 2*t/(1+t^2))=(fun t => 2*(t*rationalKernel t)) := by
    funext t
    simp only [rationalKernel,div_eq_mul_inv,mul_assoc]
  rw [he,cfc_const_mul (2:ℝ) (fun t => t*rationalKernel t) a
    (continuous_id.mul continuous_rationalKernel).continuousOn,
    cfc_mul (fun t:ℝ=>t) rationalKernel a continuous_id.continuousOn
      continuous_rationalKernel.continuousOn,cfc_id' ℝ a ha]

lemma kernel_commute {a : A} (ha : IsSelfAdjoint a) : Commute a (kernel a) := by
  have h := cfc_commute_cfc (fun t : ℝ => t) rationalKernel a
  rwa [cfc_id' ℝ a ha] at h

lemma kernel_den {a : A} (ha : IsSelfAdjoint a) : kernel a*(1+a*a)=1 := by
  have hden : cfc (fun t : ℝ => 1+t^2) a=1+a*a := by
    rw [cfc_const_add (1:ℝ) (fun t => t^2) a (continuous_id.pow 2).continuousOn ha,
      cfc_pow_id a 2 ha,pow_two,map_one]
  rw [←hden, kernel,←cfc_mul rationalKernel (fun t : ℝ => 1+t^2) a
    continuous_rationalKernel.continuousOn (continuous_const.add (continuous_id.pow 2)).continuousOn]
  have he : (fun t : ℝ => rationalKernel t*(1+t^2))=(fun _ => 1) := by
    funext t
    exact inv_mul_cancel₀ (ne_of_gt (denom_pos t))
  rw [he,cfc_const_one ℝ a ha]

lemma den_kernel {a : A} (ha : IsSelfAdjoint a) : (1+a*a)*kernel a=1 := by
  have h := congrArg star (kernel_den ha)
  simpa only [star_mul,star_add,star_one,ha.star_eq,(kernel_selfAdjoint a).star_eq] using h

lemma clip_difference {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    clip a-clip b=(2:ℝ) • (kernel a*(a-b)*kernel b)-
      clip a*(a-b)*b*kernel b := by
  have hka := kernel_commute ha
  have hab : a*kernel a-b*kernel b=
      kernel a*(a-b)*kernel b-a*kernel a*(a-b)*b*kernel b := by
    calc
      a*kernel a-b*kernel b =
        a*kernel a*((1+b*b)*kernel b)-(kernel a*(1+a*a))*b*kernel b := by
          rw [den_kernel hb,kernel_den ha,mul_one,one_mul]
      _ = _ := by noncomm_ring [hka.eq]
  rw [clip_formula ha,clip_formula hb,←smul_sub,hab,smul_sub]
  simp only [smul_mul_assoc]

def lift (a : A) : A := cfc rationalLift a

lemma lift_selfAdjoint (a : A) : IsSelfAdjoint (lift a) := cfc_predicate _ _

lemma clip_lift {a : A} (ha : IsSelfAdjoint a) (hn : ‖a‖≤1) : clip (lift a)=a := by
  nontriviality A
  rw [clip,lift,←cfc_comp rationalClip rationalLift a ha
    continuous_rationalClip.continuousOn continuous_rationalLift.continuousOn]
  calc
    cfc (rationalClip ∘ rationalLift) a = cfc (fun t:ℝ=>t) a := by
      apply cfc_congr
      intro t ht
      exact rationalClip_lift ((spectrum.norm_le_norm_of_mem ht).trans hn)
    _=a := cfc_id' ℝ a ha

end Kadison.Kaplansky

end

end
end

end OAI

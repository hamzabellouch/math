import OAI.NumberTheory.DirichletL.Moments.DyadicCount
import OAI.NumberTheory.DirichletL.Energy.Profiles
import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def weight (x:ℝ):ℝ:=cutoff (x/2)*(1-cutoff (4*x))

lemma weight_bounds (x:ℝ):0≤weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0:=by
  rw [weight,cutoff_one (4*x) (by linarith),sub_self,mul_zero]

lemma weight_zero_high (x:ℝ)(hx:2≤x):weight x=0:=by
  rw [weight,cutoff_zero (x/2) (by linarith),zero_mul]

lemma weight_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):weight x=1:=by
  rw [weight,cutoff_one (x/2) (by linarith),cutoff_zero (4*x) (by linarith)]
  norm_num

lemma weight_support:Function.support weight⊆Set.Icc (1/8:ℝ) 2:=by
  intro x hx
  exact ⟨(lt_of_not_ge (fun h=>hx (weight_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hx (weight_zero_high x h))).le⟩

lemma weight_smooth:ContDiff ℝ ∞ weight:=by
  have hc:ContDiff ℝ ∞ cutoff:=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact (hc.comp (contDiff_id.div_const 2)).mul
    (contDiff_const.sub (hc.comp (contDiff_const.mul contDiff_id)))

def profile:𝓢(ℝ,ℂ):=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x:ℝ=>(weight x:ℂ))⊆Set.Icc (1/8:ℝ) 2 from by
      intro x hx
      apply weight_support
      intro hz
      apply hx
      change (weight x:ℂ)=0
      rw [hz]
      rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp weight_smooth)

lemma profile_apply (x:ℝ):profile x=(weight x:ℂ):=rfl
lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1
lemma profile_le_one (x:ℝ):(profile x).re≤1:=(weight_bounds x).2
lemma profile_zero:profile 0=0:=by rw [profile_apply,weight_zero_low 0 (by norm_num)];rfl
lemma profile_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):profile x=1:=by
  rw [profile_apply,weight_one x hx hx'];rfl

lemma scaled_majorant (H q:ℝ)(hH:0<H)(hlo:H/4≤q)(hhi:q≤H):
    (profile (q/H)).re=1:=by
  rw [profile_one (q/H) ((le_div_iff₀ hH).mpr (by linarith))
    ((div_le_one hH).mpr hhi)]
  rfl

def bands (H:ℝ):Finset ℤ:=indices (H/8) (2*H)

lemma bands_scale (H:ℝ)(hH:0<H)(j:ℤ)(hj:j∈bands H):
    H/8≤dyadicScale j ∧ dyadicScale j≤8*H:=by
  have h:=(mem_indices_iff_scale (H/8) (2*H) (by positivity) (by positivity) j).mp hj
  constructor
  · exact h.1
  · linarith [h.2]

lemma bands_card (H:ℝ)(hH:0<H):((bands H).card:ℝ)≤7:=by
  have h:=indices_card_bound (H/8) (2*H) (by positivity) (by linarith)
  have he:(2*H)/(H/8)=16:=by field_simp;ring
  rw [he,show (16:ℝ)=(2:ℝ)^4 by norm_num,Real.logb_pow] at h
  norm_num [Real.logb_self_eq_one] at h
  change ((indices (H/8) (2*H)).card:ℝ)≤7
  exact_mod_cast h

lemma weighted_partition (H q:ℝ)(hH:0<H):
    (profile (q/H)).re=(∑j∈bands H,dyadicWeight j q)*(profile (q/H)).re:=by
  by_cases h:weight (q/H)=0
  · simp only [profile_apply,Complex.ofReal_re,h,mul_zero]
  · have hx:=weight_support h
    have hq:q∈Set.Icc (H/8) (2*H):=⟨by linarith [(le_div_iff₀ hH).mp hx.1],
      (div_le_iff₀ hH).mp hx.2⟩
    rw [bands,dyadic_partition_on_interval (H/8) (2*H) q (by positivity) hq]
    exact (one_mul _).symm

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI

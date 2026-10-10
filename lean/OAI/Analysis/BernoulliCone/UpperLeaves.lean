import OAI.Analysis.BernoulliCone.UpperLimits

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma upperSigned_pos_zero :0<upperSigned 0 := by
  rw [upperSigned_cap (by simp [Cylindrical.radiusSq,Cylindrical.axis])]
  exact smoothCap_pos_zero
lemma upperFamily_parameter_continuous (x:Space 7) :
    ContinuousOn (fun l=>upperFamily l x) (Ioi 0) := by
  intro l hl
  unfold upperFamily
  exact ((continuousAt_const.mul continuousAt_id).mul
    ((upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ (ne_of_gt hl)).smul continuousAt_const)).max continuousAt_const)).continuousWithinAt
lemma upperFamily_tendsto_atTop (x:Space 7) :
    Tendsto (fun l:ℝ=>upperFamily l x) atTop atTop := by
  have hi:Tendsto (fun l:ℝ=>l⁻¹ • x) atTop (𝓝 0) := by
    simpa only [zero_smul] using (tendsto_inv_atTop_zero: Tendsto (fun l:ℝ=>l⁻¹) atTop (𝓝 0)).smul (tendsto_const_nhds (x:=x))
  have hs:Tendsto (fun l:ℝ=>max (upperSigned (l⁻¹ • x)) 0) atTop (𝓝 (upperSigned 0)) := by
    simpa only [Function.comp_apply,max_eq_left upperSigned_pos_zero.le] using
      (upperSigned_continuous.tendsto 0 |>.comp hi).max (tendsto_const_nhds (x:=(0:ℝ)))
  exact (tendsto_id.const_mul_atTop κ_pos).atTop_mul_pos upperSigned_pos_zero hs
lemma U_le_upperFamily (x:Space 7) {l:ℝ} (hl:0<l) : U x≤upperFamily l x := by
  apply le_of_tendsto (upperFamily_tendsto_zero x)
  have hh:∀ᶠ s:ℝ in 𝓝[>] 0,s<l := (gt_mem_nhds hl).filter_mono nhdsWithin_le_nhds
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hp
  exact upperFamily_monotone x hp hl hs.le
lemma existsUnique_upper_leaf (x:Space 7) {t:ℝ} (ht:U x<t) :
    ∃! l:ℝ, 0<l ∧ upperFamily l x=t := by
  have htpos:0<t:=(U_nonneg x).trans_lt ht
  obtain ⟨a,ha,hat⟩:∃a:ℝ,0<a ∧ upperFamily a x<t := by
    have hh:∀ᶠ a:ℝ in 𝓝[>] 0,0<a ∧ upperFamily a x<t := by
      filter_upwards [self_mem_nhdsWithin,(upperFamily_tendsto_zero x).eventually (gt_mem_nhds ht)] with a ha ha1
      exact ⟨ha,ha1⟩
    exact hh.exists
  obtain ⟨b,hab,hbt⟩:∃b:ℝ,a<b ∧ t<upperFamily b x := by
    exact ((eventually_gt_atTop a).and ((upperFamily_tendsto_atTop x).eventually (eventually_gt_atTop t))).exists
  have hb:0<b:=ha.trans hab
  obtain ⟨l,hlI,hle⟩:=intermediate_value_Icc hab.le
    ((upperFamily_parameter_continuous x).mono (fun y hy=>ha.trans_le hy.1)) ⟨hat.le,hbt.le⟩
  change upperFamily l x=t at hle
  have hl:0<l:=ha.trans_le hlI.1
  refine ⟨l,⟨hl,hle⟩,?_⟩
  rintro s ⟨hs,hse⟩
  rcases lt_trichotomy s l with h|h|h
  · have hh:=upperFamily_strict hs h (by rw [hse]; exact htpos)
    rw [hse,hle] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh:=upperFamily_strict hl h (by rw [hle]; exact htpos)
    rw [hse,hle] at hh
    exact False.elim (lt_irrefl _ hh)
/-- Leaf parameter above the minimizer candidate. Its defining equation is proved
from the actual glued DSJ profiles; it is not a new foliation assumption. -/
def upperParameter (x:Space 7) (t:ℝ) :ℝ :=
  if h:U x<t then (existsUnique_upper_leaf x h).exists.choose else 0
lemma upperParameter_spec {x:Space 7} {t:ℝ} (ht:U x<t) :
    0<upperParameter x t ∧ upperFamily (upperParameter x t) x=t := by
  rw [upperParameter,dite_eq_left ht]
  exact (existsUnique_upper_leaf x ht).exists.choose_spec
lemma upperParameter_unique {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) (he:upperFamily l x=t) :
    upperParameter x t=l := by
  exact ExistsUnique.unique (existsUnique_upper_leaf x ht) (upperParameter_spec ht) ⟨hl,he⟩
lemma upperParameter_lt_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    upperParameter x t<l ↔ t<upperFamily l x := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    rw [←he]
    exact upperFamily_strict hp h (by rw [he]; exact (U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hl hp (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
lemma lt_upperParameter_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    l<upperParameter x t ↔ upperFamily l x<t := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    by_cases hw:0<upperFamily l x
    · rw [←he]; exact upperFamily_strict hl h hw
    · exact (le_of_not_gt hw).trans_lt ((U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hp hl (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
end Bernoulli.DeSilvaJerison

end
end

end OAI

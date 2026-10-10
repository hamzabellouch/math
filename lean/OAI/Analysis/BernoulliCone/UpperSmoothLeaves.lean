import OAI.Analysis.BernoulliCone.ScalarImplicit

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperSigned_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≠1) :
    ContDiffAt ℝ ∞ upperSigned x := by
  have hcont:ContinuousAt (Cylindrical.radiusSq axis) x :=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  rcases lt_or_gt_of_ne hq with h|h
  · apply (smoothCap_contDiffAt h.le).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (gt_mem_nhds h)] with y hy
    exact upperSigned_cap hy.le
  · have hqp:0<Cylindrical.radiusSq axis x:=by linarith
    obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
    apply (outerSigned_contDiffAt hx ha).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (lt_mem_nhds h)] with y hy
    exact upperSigned_outer hy.le
lemma upperFamily_joint_contDiffAt {p:ℝ×Space 7} (hl:0<p.1)
    (hp:0<upperFamily p.1 p.2) (hq:Cylindrical.radiusSq axis (p.1⁻¹ • p.2)≠1) :
    ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) p := by
  have hpos:0<upperSigned (p.1⁻¹ • p.2) := by
    have hh:0 < max (upperSigned (p.1⁻¹ • p.2)) 0:=
      pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have hi:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>z.1⁻¹ • z.2) p:=
    (contDiffAt_fst.inv hl.ne').smul contDiffAt_snd
  have hs0 : ContDiffAt ℝ ∞ upperSigned (p.1⁻¹ • p.2) :=
    upperSigned_contDiffAt hq
  have hs:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperSigned (z.1⁻¹ • z.2)) p := by
    exact ContDiffAt.comp (f:=fun z:ℝ×Space 7=>z.1⁻¹ • z.2) (g:=upperSigned) p hs0 hi
  apply ((contDiffAt_const.mul contDiffAt_fst).mul hs).congr_of_eventuallyEq
  filter_upwards [hs.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
  exact congrArg (κ*z.1* ·) (max_eq_left hz.le)
lemma upperFamily_scale_derivative {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ∃ρ:ℝ,0<ρ ∧ HasDerivAt (fun s:ℝ=>upperFamily s x) ρ l := by
  let ρ:=κ*(upperSigned (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient upperSigned (l⁻¹ • x)))
  have hd:HasDerivAt (upperTrace x) ρ l := by
    have hh:HasDerivAt (fun s:ℝ=>κ*(s*upperSigned (s⁻¹ • x))) ρ l:=
      (Foliation.hasDerivAt_dilate x hl.ne'
        ((upperSigned_contDiffAt hq).differentiableAt (by simp))).const_mul κ
    change HasDerivAt (fun s=>κ*s*upperSigned (s⁻¹ • x)) ρ l
    simpa only [mul_assoc] using hh
  have hpt:0<upperTrace x l := by rw [upperFamily_eq_max hl.le x] at hp; simpa using hp
  obtain ⟨v,hv,hdv⟩:=upperTrace_right_derivative x hl hpt
  have he:ρ=v:=(uniqueDiffWithinAt_Ici l).eq_deriv (Ici l) hd.hasDerivWithinAt hdv
  refine ⟨ρ,he.symm ▸ hv,?_⟩
  apply hd.congr_of_eventuallyEq
  have hln:∀ᶠ s:ℝ in 𝓝 l,0<s:=lt_mem_nhds hl
  have hpn:∀ᶠ s:ℝ in 𝓝 l,0<upperTrace x s:=hd.continuousAt.eventually (lt_mem_nhds hpt)
  filter_upwards [hln,hpn] with s hs hs1
  rw [upperFamily_eq_max hs.le,max_eq_left hs1.le]
lemma upperParameter_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have ht:0<p.2:=(U_nonneg p.1).trans_lt hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>upperFamily z.2 z.1.1-z.1.2
  have hpl:0<upperFamily l p.1 := by rw [he]; exact ht
  have hUF:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,p.1) :=
    upperFamily_joint_contDiffAt (p:=(l,p.1)) hl hpl hq
  have hF:ContDiffAt ℝ ∞ F (p,l) := by
    have hh:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>(z.2,z.1.1)) (p,l):=by fun_prop
    exact (hUF.comp (p,l) hh).sub
      (contDiffAt_fst.snd)
  obtain ⟨ρ,hρ,hd⟩:=upperFamily_scale_derivative hl hpl hq
  have hdF:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l:=by simpa only [F] using hd.sub_const p.2
  obtain ⟨ψ,hψ,hψ0,hψeq⟩:=Foliation.scalar_implicit hF hdF hρ.ne'
  have hF0:F (p,l)=0:=by dsimp [F]; rw [he,sub_self]
  apply hψ.congr_of_eventuallyEq
  have hψpos:∀ᶠ z in 𝓝 p,0<ψ z:=hψ.continuousAt.eventually (lt_mem_nhds (by rwa [hψ0]))
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt continuous_snd.continuousAt hp
  filter_upwards [hψeq,hψpos,hdom] with z hz hz1 hz2
  rw [hF0] at hz
  exact upperParameter_unique hz2 hz1 (sub_eq_zero.mp hz)
end Bernoulli.DeSilvaJerison

end
end

end OAI

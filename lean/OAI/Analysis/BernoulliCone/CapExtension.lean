import OAI.Analysis.BernoulliCone.BoundedCalibration

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_eq_cap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≤1) :
    upperFamily l x=κ*l*smoothCap (l⁻¹ • x) := by
  have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=
    pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
  have hs:0<upperSigned (l⁻¹ • x):=by simpa using hh
  rw [upperFamily,max_eq_left hs.le,upperSigned_cap hq]

/-- Smooth signed extensions of the inverse cap parameter through the actual
cap/exterior interface, obtained by IFT with local uniqueness. -/
lemma capParameter_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃ψ:Space 7×ℝ→ℝ,ContDiffAt ℝ ∞ ψ p ∧ ψ p=upperParameter p.1 p.2 ∧
      ∀ᶠ z in 𝓝 p, U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 →
        ψ z=upperParameter z.1 z.2 := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have hpos:0<upperFamily l p.1:=he.symm ▸ (U_nonneg p.1).trans_lt hp
  have hc:ContDiffAt ℝ ∞ smoothCap (l⁻¹ • p.1):=smoothCap_contDiffAt hq
  have hpc:0<smoothCap (l⁻¹ • p.1):=by
    rw [←upperSigned_cap hq]
    exact upperParameter_signed_pos hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>κ*z.2*smoothCap (z.2⁻¹ • z.1.1)-z.1.2
  have hi:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>z.2⁻¹ • z.1.1) (p,l):=
    (contDiffAt_snd.inv hl.ne').smul (contDiffAt_fst.fst)
  have hF:ContDiffAt ℝ ∞ F (p,l):=
    ((contDiffAt_const.mul contDiffAt_snd).mul (hc.comp (p,l) hi)).sub contDiffAt_fst.snd
  let ρ:=κ*(smoothCap (l⁻¹ • p.1)-inner ℝ (l⁻¹ • p.1) (gradient smoothCap (l⁻¹ • p.1)))
  have hρ:0<ρ:=mul_pos κ_pos (smoothCap_radial_defect_pos hq hpc)
  have hd:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l := by
    have hh:=((Foliation.hasDerivAt_dilate p.1 hl.ne'
      (hc.differentiableAt (by simp))).const_mul κ).sub_const p.2
    simpa only [F,mul_assoc] using hh
  obtain ⟨ψ,hψ,hψ0,hψeq,huniq⟩:=Foliation.scalar_implicit_unique hF hd hρ.ne'
  refine ⟨ψ,hψ,hψ0,?_⟩
  have hF0:F (p,l)=0:=by
    dsimp [F]
    rw [←upperFamily_eq_cap hl hpos hq,he,sub_self]
  have ht:Tendsto (fun z:Space 7×ℝ=>(z,upperParameter z.1 z.2)) (𝓝 p) (𝓝 (p,l)):=
    tendsto_id.prodMk_nhds (upperParameter_continuousAt hp)
  filter_upwards [ht.eventually huniq] with z hz hzp hzq
  apply hz.mp
  rw [hF0]
  dsimp [F]
  have hzpos:0<upperFamily (upperParameter z.1 z.2) z.1:=
    (upperParameter_spec hzp).2.symm ▸ (U_nonneg z.1).trans_lt hzp
  rw [←upperFamily_eq_cap (upperParameter_spec hzp).1 hzpos hzq,
    (upperParameter_spec hzp).2,sub_self]

lemma gradient_smoothCap_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1) :
    ContDiffAt ℝ ∞ (gradient smoothCap) x := by
  exact (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp x
    ((smoothCap_contDiffAt hq).fderiv_right (by simp))

/-- The actual one-sided cap flux admits a smooth germ even at the seam.
No regularity of the discontinuous full flux is asserted. -/
theorem upperFlux_cap_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃B:Space 7×ℝ→Space 7,ContDiffAt ℝ ∞ B p ∧ B p=upperFlux p ∧
      ∀ᶠ z in 𝓝 p,U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 → B z=upperFlux z := by
  obtain ⟨ψ,hψ,hψ0,he⟩:=capParameter_local_extension hp hq
  let B:Space 7×ℝ→Space 7:=fun z=>κ • gradient smoothCap ((ψ z)⁻¹ • z.1)
  have hψp:ψ p≠0:=by rw [hψ0]; exact (upperParameter_spec hp).1.ne'
  have hn:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(ψ z)⁻¹ • z.1) p:=
    (hψ.inv hψp).smul contDiffAt_fst
  have hg:ContDiffAt ℝ ∞ (gradient smoothCap) ((ψ p)⁻¹ • p.1):=by
    rw [hψ0]; exact gradient_smoothCap_contDiffAt hq
  refine ⟨B,(hg.comp p hn).const_smul κ,?_,?_⟩
  · simp only [B,hψ0,upperFlux,ite_eq_left hp,ite_eq_left hq]
  · filter_upwards [he] with z hz hzp hzq
    simp only [B,hz hzp hzq,upperFlux,ite_eq_left hzp,ite_eq_left hzq]
end Bernoulli.DeSilvaJerison

end
end

end OAI

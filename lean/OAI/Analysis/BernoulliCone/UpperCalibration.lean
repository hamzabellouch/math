import OAI.Analysis.BernoulliCone.LaplacianDilation

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma upperSigned_laplacian_nonpos {x:Space 7}
    (hp:0<upperSigned x) (hq:Cylindrical.radiusSq axis x≠1) : Δ upperSigned x≤0 := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  rcases lt_or_gt_of_ne hq with h|h
  · have he:upperSigned =ᶠ[𝓝 x] smoothCap := by
      filter_upwards [hc.eventually (gt_mem_nhds h)] with y hy
      exact upperSigned_cap hy.le
    rw [(laplacian_congr_nhds he).self_of_nhds]
    have hp':0<smoothCap x:=by rwa [upperSigned_cap h.le] at hp
    have hv:= (CapAlgebra.V_bounds (Cylindrical.radiusSq_nonneg axis x axis_norm)
      h.le capB_bounds.1 capB_bounds.2).1
    have hy:=CapAlgebra.Y_pos (Cylindrical.radiusSq_nonneg axis x axis_norm) hv capC_pos
    have hs:0<capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB) := by
      change 0<CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹) at hp'
      rw [←div_eq_mul_inv] at hp'
      exact pos_of_mul_pos_right hp' hy.le
    exact smoothCap_laplacian_nonpos h.le ((capH_pos_iff _).mp hs).le
  · have he:upperSigned =ᶠ[𝓝 x] outerSigned := by
      filter_upwards [hc.eventually (lt_mem_nhds h)] with y hy
      exact upperSigned_outer hy.le
    obtain ⟨hx,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by linarith)
    rw [(laplacian_congr_nhds he).self_of_nhds,outerSigned_laplacian hx ha]

lemma upperFamily_laplacian_nonpos {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    Δ (upperFamily l) x≤0 := by
  have hpos:0<upperSigned (l⁻¹ • x) := by
    have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have hf:ContDiffAt ℝ 2 upperSigned (l⁻¹ • x):=(upperSigned_contDiffAt hq).of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hi:ContDiffAt ℝ 2 (fun y:Space 7=>l⁻¹ • y) x:=
    (contDiffAt_id (𝕜:=ℝ) (n:=2) (x:=x)).const_smul l⁻¹
  have hg:ContDiffAt ℝ 2 (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=
    ContDiffAt.comp (f:=fun y:Space 7=>l⁻¹ • y) x hf hi
  have he:(upperFamily l) =ᶠ[𝓝 x] (fun y=>κ*l*upperSigned (l⁻¹ • y)) := by
    filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
    exact congrArg (κ*l* ·) (max_eq_left hy.le)
  rw [(laplacian_congr_nhds he).self_of_nhds]
  have hh:Δ (fun y:Space 7=>κ*l*upperSigned (l⁻¹ • y)) x=
      κ*l*Δ (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=laplacian_smul (κ*l) hg
  rw [hh,ScalarLaplacian.laplacian_comp_smul l⁻¹ hf]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg κ_pos.le hl.le)
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (upperSigned_laplacian_nonpos hpos hq))

lemma upperFamily_contDiffAt_swap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperFamily z.2 z.1) (x,l) := by
  have hh:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,x):=
    upperFamily_joint_contDiffAt (p:=(l,x)) hl hp hq
  have hi:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(z.2,z.1)) (x,l):=
    contDiffAt_snd.prodMk contDiffAt_fst
  exact ContDiffAt.comp (f:=fun z:Space 7×ℝ=>(z.2,z.1)) (x,l) hh hi

/-- The actual upper foliation's spatial gradient at a point above the cone. -/
def upperCalibration (p:Space 7×ℝ) : Space 7 :=
  Foliation.spatialGradient (fun z:Space 7×ℝ=>upperFamily z.2 z.1)
    (p.1,upperParameter p.1 p.2)

lemma upperCalibration_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ upperCalibration p := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hF:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperFamily z.2 z.1)
      (p.1,upperParameter p.1 p.2):=by
    exact upperFamily_contDiffAt_swap hl (by rw [he]; exact (U_nonneg _).trans_lt hp) hq
  exact (Foliation.spatialGradient_contDiffAt hF).comp p
    (contDiffAt_fst.prodMk (upperParameter_contDiffAt hp hq))

theorem upperCalibration_bulk {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    Foliation.divergence (fun x=>upperCalibration (x,p.2)) p.1+
      inner ℝ (upperCalibration p) (deriv (fun t=>upperCalibration (p.1,t)) p.2)≤0 := by
  let F:Space 7×ℝ→ℝ:=fun z=>upperFamily z.2 z.1
  let L:Space 7×ℝ→ℝ:=fun z=>upperParameter z.1 z.2
  have hl:0<L p:=(upperParameter_spec hp).1
  have heq:upperFamily (L p) p.1=p.2:=(upperParameter_spec hp).2
  have hpos:0<upperFamily (L p) p.1:=by rw [heq]; exact (U_nonneg _).trans_lt hp
  have hF:ContDiffAt ℝ ∞ F (p.1,L p):=by
    exact upperFamily_contDiffAt_swap hl hpos hq
  have hL:ContDiffAt ℝ ∞ L p:=upperParameter_contDiffAt hp hq
  have he:∀ᶠ z:Space 7×ℝ in 𝓝 p,F (z.1,L z)=z.2:=by
    have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2:=
      (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
        continuous_snd.continuousAt hp
    filter_upwards [hn] with z hz
    exact (upperParameter_spec hz).2
  obtain ⟨ρ,hρ,hd⟩:=upperFamily_scale_derivative hl hpos hq
  have hρ':fderiv ℝ F (p.1,L p) (0,1)≠0:=by
    have his:HasDerivAt (fun t:ℝ=>(p.1,t)) (0,1) (L p):=by
      simpa using (hasDerivAt_const (L p) p.1).prodMk (hasDerivAt_id (L p))
    have hh:HasDerivAt (fun t:ℝ=>upperFamily t p.1) (fderiv ℝ F (p.1,L p) (0,1)) (L p):=by
      exact (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (L p) his
    exact (hh.unique hd).symm ▸ hρ.ne'
  have hid:=Foliation.foliation_divergence hF hL he hρ'
  change Foliation.divergence (fun x=>upperCalibration (x,p.2)) p.1+
    inner ℝ (upperCalibration p) (deriv (fun t=>upperCalibration (p.1,t)) p.2)=
      Δ (upperFamily (L p)) p.1 at hid
  rw [hid]
  exact upperFamily_laplacian_nonpos hl hpos hq
end Bernoulli.DeSilvaJerison

end
end

end OAI

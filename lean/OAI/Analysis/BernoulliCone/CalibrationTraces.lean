import OAI.Analysis.BernoulliCone.OuterSlope

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma gradient_dilation {f:Space 7→ℝ} {x:Space 7} {l:ℝ} (hl:l≠0)
    (hf:DifferentiableAt ℝ f (l⁻¹ • x)) :
    gradient (fun y=>κ*l*f (l⁻¹ • y)) x=κ • gradient f (l⁻¹ • x) := by
  have hd:HasFDerivAt (fun y:Space 7=>l⁻¹ • y)
      (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)) x := (hasFDerivAt_id x).const_smul l⁻¹
  have hh:HasFDerivAt (fun y:Space 7=>κ*l*f (l⁻¹ • y))
      ((κ*l) • (fderiv ℝ f (l⁻¹ • x) ∘L (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)))) x :=
    (hf.hasFDerivAt.comp x hd).const_mul (κ*l)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,hh.fderiv,real_inner_smul_left,inner_gradient_left]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp

lemma upperFamily_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    gradient (upperFamily l) x=κ • gradient upperSigned (l⁻¹ • x) := by
  have hf:ContDiffAt ℝ ∞ upperSigned (l⁻¹ • x):=upperSigned_contDiffAt hq
  have hs:ContinuousAt (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=
    hf.continuousAt.comp ((continuous_id.const_smul l⁻¹).continuousAt)
  have hpos:0<upperSigned (l⁻¹ • x):=by
    have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*l*upperSigned (l⁻¹ • y)) := by
    filter_upwards [hs.eventually (lt_mem_nhds hpos)] with y hy
    exact congrArg (κ*l* ·) (max_eq_left hy.le)
  rw [gradient,he.fderiv_eq]
  exact gradient_dilation hl.ne' (hf.differentiableAt (by simp))

lemma upperCalibration_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperCalibration p=κ • gradient upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by rw [he]; exact (U_nonneg _).trans_lt hp
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hq).differentiableAt (by simp))]
  exact upperFamily_gradient hl hpos hq

lemma capH_eq_zero_iff (s:ℝ) : capH s=0 ↔ |s|=3/4 := by
  constructor
  · intro hs
    have h1:(|s|≤3/4):=(capH_nonneg_iff s).mp (le_of_eq hs.symm)
    have h2:¬|s|<3/4:=by intro h; have hp:=(capH_pos_iff s).mpr h; rw [hs] at hp; exact lt_irrefl _ hp
    exact le_antisymm h1 (not_lt.mp h2)
  · intro hs
    have h1:0≤capH s:=(capH_nonneg_iff s).mpr hs.le
    have h2:¬0<capH s:=by intro h; have hp:=(capH_pos_iff s).mp h; rw [hs] at hp; exact lt_irrefl _ hp
    exact le_antisymm (not_lt.mp h2) h1

lemma smoothCap_zero_slope {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1)
    (hz:smoothCap x=0) : ‖gradient smoothCap x‖^2<c7 := by
  have hq0:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<CapAlgebra.V (Cylindrical.radiusSq axis x) capB:=
    (CapAlgebra.V_bounds hq0 hq capB_bounds.1 capB_bounds.2).1
  have hY:0<CapAlgebra.Y (Cylindrical.radiusSq axis x) capB capC:=
    CapAlgebra.Y_pos hq0 hv capC_pos
  have hh:capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB)=0 := by
    change CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹)=0 at hz
    simpa only [div_eq_mul_inv] using (mul_eq_zero.mp hz).resolve_left hY.ne'
  exact smoothCap_boundary_slope_lt hq ((capH_eq_zero_iff _).mp hh)

lemma normalized_slope_lt {G:Space 7} (hG:‖G‖^2<c7) : ‖κ • G‖^2<1 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,←κ_sq]
  exact mul_lt_mul_of_pos_left hG (sq_pos_of_pos κ_pos)

theorem upper_free_boundary_slopes {x:Space 7} (hz:upperSigned x=0) :
    (Cylindrical.radiusSq axis x≤1 → ‖κ • gradient smoothCap x‖^2<1) ∧
    (1≤Cylindrical.radiusSq axis x → ‖κ • gradient outerSigned x‖^2<1) := by
  constructor
  · intro hq
    exact normalized_slope_lt (smoothCap_zero_slope hq (by rwa [upperSigned_cap hq] at hz))
  · intro hq
    exact normalized_slope_lt (outer_zero_slope_lt hq (by rwa [upperSigned_outer hq] at hz))
end Bernoulli.DeSilvaJerison

end
end

end OAI

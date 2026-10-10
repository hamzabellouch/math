import OAI.Geometry.Convex.GeneralMahler.Rigid.Basis

namespace OAI
/-! Lipschitz/homogeneous with diagonal Jacobian a.e. ⇒
separate coordinates. Uses smoothG (gaussian averaging, §02). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open Layers
variable {m:ℕ}
private lemma lp_homo (C:ProperCone ℝ (Rn m)) {r:ℝ} (hr:0<r) (x:Rn m):
    coneProj C (r • x)=r • coneProj C x := by
  let A := coneProj C x
  apply proj_unique C (C.smul_mem (proj_mem C _) hr.le)
  intro y hy
  have he := proj_vi C x (C.smul_mem hy (inv_pos.mpr hr).le)
  have hh : y-r • A=r • (r⁻¹ • y-A) := by rw [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  change ⟪r • x-r • A,y-r • A⟫≤_
  rw [hh,← smul_sub,real_inner_smul_left,real_inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hr.le (mul_nonpos_of_nonneg_of_nonpos hr.le he)

lemma lp_same_smooth (g:Rn m→ℝ) {K:ℝ≥0} (hk:LipschitzWith K g)
    (x v:Rn m)
    (hh:∀ᵐ y:Rn m,fderiv ℝ g y v=0) : smoothG g x=smoothG g (x+v) := by
  let f := fun t:ℝ=> x+t • v
  have he (t:ℝ) : HasDerivAt (smoothG g ∘ f) 0 t := by
    obtain ⟨h,h'⟩:= smoothG_derivative_lipschitz hk (f t)
    have hd : HasDerivAt f v t := by
      convert ((hasDerivAt_const t x).fun_add ((hasDerivAt_id' t).smul_const v)) using 1
      first | rfl | simp
    have hp := h'.comp_hasDerivAt _ hd
    rw [ContinuousLinearMap.integral_apply h] at hp
    have ht : ∀ᵐ y∂normal m,fderiv ℝ g (y+f t) v=0 :=
      normal_ac.ae_le ((measurePreserving_add_right volume (f t)).quasiMeasurePreserving.tendsto_ae.eventually hh)
    rw [show (∫ y,fderiv ℝ g (y+f t) v ∂normal m)=0 from integral_eq_zero_of_ae ht] at hp
    exact hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>he t)
    (continuous_const.intervalIntegrable 0 1)
  simp only [intervalIntegral.integral_zero,Function.comp_apply,f,zero_smul,one_smul,add_zero] at hi
  exact (sub_eq_zero.mp hi.symm).symm

lemma lp_mean_close (g:Rn m→ℝ) {K:ℝ≥0} (hk:LipschitzWith K g) (x:Rn m):
    ‖smoothG g x-g x‖ ≤ (∫ y:Rn m,(K:ℝ)*‖y‖ ∂normal m) := by
  let f := fun y:Rn m=>g (y+x)
  let L := fun y:Rn m=>(K:ℝ)*‖y‖
  have hc : Continuous f := hk.continuous.comp (continuous_id.add continuous_const)
  have hi : PolyBound f := (PolyBound.lipschitz hk).comp ((PolyBound.id).add (PolyBound.const _))
  have hv : Integrable f (normal m) := hi.gaussian_integrable hc.aestronglyMeasurable
  have ie : Integrable L (normal m) := (((PolyBound.const _).mul (PolyBound.id.norm)).gaussian_integrable
    (continuous_const.mul (continuous_norm (E:=Rn m))).aestronglyMeasurable)
  let j:= fun y:Rn m=> f y-g x
  have hh (y) : ‖j y‖≤ L y := by
    have he:=hk.dist_le_mul (y+x) x
    simpa only [dist_eq_norm,add_sub_cancel_right] using he
  have he : smoothG g x-g x=∫ y,j y ∂normal m := by
    unfold j; rw [integral_sub hv (integrable_const _)]
    simp; rfl
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono (show Integrable j (normal m) from hv.sub (integrable_const _)).norm ie hh

variable (C:ProperCone ℝ (Rn m)) (b:Basis (Fin m) ℝ (Rn m))
lemma lp_comp (h:diagDeriv C b) (i:Fin m) (x y:Rn m) (he:b.coord i x=b.coord i y):
    b.coord i (coneProj C x)=b.coord i (coneProj C y) := by
  let B: Rn m→L[ℝ]ℝ := (b.coord i).toContinuousLinearMap
  let g := fun x:Rn m=>B (coneProj C x)
  let K := ‖B‖₊*1
  have hk : LipschitzWith K g:= B.lipschitzWith.comp (coneProj_lip C)
  let M := ∫ y:Rn m,(K:ℝ)*‖y‖ ∂normal m
  have hv (v:Rn m) (he:B v=0) : ∀ᵐ t:Rn m,fderiv ℝ g t v=0 := by
    filter_upwards [h,(coneProj_lip C).ae_differentiableAt] with t ht hp
    let d := fderiv ℝ (coneProj C) t
    have hd : fderiv ℝ g t = B.comp d := (B.hasFDerivAt.comp t hp.hasFDerivAt).fderiv
    rw [hd]
    conv_lhs => rw [← b.sum_repr v, _root_.map_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [_root_.map_smul,ContinuousLinearMap.comp_apply]
    obtain ⟨l,hl⟩:=ht j
    rw [show d (b j)=_ from hl,_root_.map_smul]
    by_cases h:i=j
    · subst j; change b.repr v i • _=_
      change b.repr v i = 0 at he; rw [he,zero_smul]
    have h' : B (b j)=0 := by
      change b.coord i (b j)=0
      simp [h]
    rw [h',smul_zero,smul_zero]
  have hh (r:ℝ) (hr:0<r) : r*‖g x-g y‖ ≤ 2*M := by
    let u := r • y-r • x
    have hb : B u=0 := by
      unfold u; rw [_root_.map_sub,_root_.map_smul,_root_.map_smul]
      change r • b.coord i y-r • b.coord i x=0
      rw [he,sub_self]
    have ht := lp_same_smooth g hk (r • x) u (hv u hb)
    have hu : r • x+u=r • y := by unfold u; abel
    rw [hu] at ht
    have hp (x:Rn m) : g (r • x)=r • g x := by unfold g; rw [lp_homo C hr,_root_.map_smul]
    have hi := norm_sub_le (g (r • x)-smoothG g (r • x)) (g (r • y)-smoothG g (r • y))
    rw [norm_sub_rev (g _), norm_sub_rev (g (r • y))] at hi
    have ha : g (r • x)-smoothG g (r • x)-(g (r • y)-smoothG g (r • y))=
        r • (g x-g y) := by rw [ht,hp,hp,smul_sub]; abel
    rw [ha,norm_smul,Real.norm_of_nonneg hr.le] at hi
    have hh (x:Rn m): ‖smoothG g x-g x‖ ≤ M:= lp_mean_close g hk _
    linarith [hh (r • x),hh (r • y)]
  change g x=g y
  by_contra hx
  have ht : 0 < ‖g x-g y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hp : 0<M := by linarith [hh 1 zero_lt_one]
  have hi := hh ((2*M+1)/‖g x-g y‖) (by positivity)
  rw [div_mul_cancel₀ _ ht.ne'] at hi
  linarith
end GeneralMahler

end

end OAI

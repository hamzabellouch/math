import OAI.Analysis.BernoulliCone.ScalarLaplacian

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
open ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
def axis (e x:E) : ℝ := inner ℝ x e
def transverse (e x:E) : E := x-axis e x • e
def radiusSq (e x:E) : ℝ := ‖x‖^2-(axis e x)^2

omit [FiniteDimensional ℝ E] in
theorem transverse_inner [FiniteDimensional ℝ E] (e x:E) (he:‖e‖=1) : inner ℝ (transverse e x) e=0 := by
  simp [transverse,axis,inner_sub_left,real_inner_smul_left,he]
omit [FiniteDimensional ℝ E] in
theorem transverse_sq [FiniteDimensional ℝ E] (e x:E) (he:‖e‖=1) : ‖transverse e x‖^2=radiusSq e x := by
  rw [transverse,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,he,
    real_inner_smul_right]
  unfold radiusSq axis
  ring
lemma radiusSq_nonneg (e x:E) (he:‖e‖=1) : 0≤radiusSq e x := by
  rw [←transverse_sq e x he]; positivity
omit [FiniteDimensional ℝ E] in
lemma axis_contDiff [FiniteDimensional ℝ E] (e:E) {n:WithTop ℕ∞} : ContDiff ℝ n (axis e) := contDiff_id.inner ℝ contDiff_const
lemma radiusSq_contDiff (e:E) {n:WithTop ℕ∞} : ContDiff ℝ n (radiusSq e) :=
  (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=n)).sub ((axis_contDiff e).pow 2)
lemma gradient_axis (e x:E) : gradient (axis e) x=e := by
  apply ext_inner_right ℝ
  intro v
  rw [←line_deriv (axis_contDiff e (n:=1) |>.differentiable (by norm_num) x) v]
  have hh:=Axisymmetric.hasDerivAt_axis x v e 0
  change deriv (fun t:ℝ=>inner ℝ (x+t • v) e) 0 = _
  rw [hh.deriv,real_inner_comm]
lemma gradient_norm_sq (x:E) : gradient (fun z:E=>‖z‖^2) x=(2:ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [←line_deriv (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=1) |>.differentiable (by norm_num) x) v]
  have hl : HasDerivAt (fun t:ℝ=>x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  rw [hl.norm_sq.deriv]
  simp [real_inner_smul_left]
lemma laplacian_axis (e x:E) : Δ (axis e) x=0 := by
  rw [laplacian_sum_line (axis_contDiff e).contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hh : deriv (fun t:ℝ=>axis e (x+t • stdOrthonormalBasis ℝ E i))=
      fun _=>inner ℝ (stdOrthonormalBasis ℝ E i) e := by
    funext t; exact (Axisymmetric.hasDerivAt_axis x _ e t).deriv
  rw [hh,deriv_const]
lemma laplacian_norm_sq (x:E) : Δ (fun z:E=>‖z‖^2) x=2*(Module.finrank ℝ E : ℝ) := by
  rw [laplacian_sum_line (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=2)).contDiffAt]
  have hh (v:E) : deriv (deriv (fun t:ℝ=>‖x+t • v‖^2)) 0=2*‖v‖^2 := by
    have hl (t:ℝ) : HasDerivAt (fun s:ℝ=>x+s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have he : deriv (fun t:ℝ=>‖x+t • v‖^2)=fun t=>2*inner ℝ (x+t • v) v := by
      funext t; exact (hl t).norm_sq.deriv
    rw [he]
    have hd:=((hl 0).inner ℝ (hasDerivAt_const (0:ℝ) v)).const_mul 2
    simpa using hd.deriv
  simp_rw [hh]
  simp [mul_comm]
lemma gradient_radiusSq (e x:E) : gradient (radiusSq e) x=(2:ℝ) • transverse e x := by
  have ha := (axis_contDiff e (n:=1)).differentiable (by norm_num) x
  have hn := (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=1)).differentiable (by norm_num) x
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  change (fderiv ℝ (fun z:E=>‖z‖^2-(axis e z)^2) x) v = _
  have hh:=hn.hasFDerivAt.sub (ha.hasFDerivAt.pow 2)
  change (fderiv ℝ ((fun z:E=>‖z‖^2)-(fun z:E=>(axis e z)^2)) x) v = _
  rw [hh.fderiv]
  simp only [sub_apply,smul_apply]
  rw [←inner_gradient_left,gradient_norm_sq,←inner_gradient_left,gradient_axis]
  dsimp [transverse]
  simp only [real_inner_smul_left,inner_sub_left]
  ring
lemma laplacian_radiusSq (e x:E) (he:‖e‖=1) : Δ (radiusSq e) x=2*((Module.finrank ℝ E : ℝ)-1) := by
  have hφ : ContDiffAt ℝ 2 (fun s:ℝ=>s^2) (axis e x) := contDiffAt_id.pow 2
  have hh:=laplacian_comp hφ (axis_contDiff e).contDiffAt
  have hder : deriv (fun s:ℝ=>s^2) = fun s=>2*s := by funext s; simp
  have hder2 : deriv (deriv (fun s:ℝ=>s^2)) (axis e x)=2 := by rw [hder]; simp
  rw [hder2,gradient_axis,he,laplacian_axis] at hh
  change Δ ((fun z:E=>‖z‖^2)-(fun z:E=>(axis e z)^2)) x = _
  rw [(contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=2)).contDiffAt.laplacian_sub ((axis_contDiff e).pow 2).contDiffAt,
    laplacian_norm_sq,hh]
  ring

/-- A smooth cylindrical cap, expressed using the squared transverse radius so
that the symmetry axis is included without a singular-coordinate convention. -/
def lift (e:E) (y k h:ℝ→ℝ) (x:E) : ℝ := y (radiusSq e x)*h (axis e x*k (radiusSq e x))
lemma contDiffAt_lift {e x:E} {y k h:ℝ→ℝ} {n:WithTop ℕ∞}
    (hy:ContDiffAt ℝ n y (radiusSq e x)) (hk:ContDiffAt ℝ n k (radiusSq e x))
    (hh:ContDiffAt ℝ n h (axis e x*k (radiusSq e x))) : ContDiffAt ℝ n (lift e y k h) x := by
  exact (hy.comp x (radiusSq_contDiff e).contDiffAt).mul
    (hh.comp x ((axis_contDiff e).contDiffAt.mul (hk.comp x (radiusSq_contDiff e).contDiffAt)))

lemma gradient_lift {e x:E} {y k h:ℝ→ℝ}
    (hy:DifferentiableAt ℝ y (radiusSq e x)) (hk:DifferentiableAt ℝ k (radiusSq e x))
    (hh:DifferentiableAt ℝ h (axis e x*k (radiusSq e x))) :
    gradient (lift e y k h) x =
      (2*deriv y (radiusSq e x)*h (axis e x*k (radiusSq e x))) • transverse e x+
      (y (radiusSq e x)*deriv h (axis e x*k (radiusSq e x))) •
        (k (radiusSq e x) • e+(2*axis e x*deriv k (radiusSq e x)) • transverse e x) := by
  have hq: DifferentiableAt ℝ (radiusSq e) x :=
    (radiusSq_contDiff e (n:=1)).differentiable (by norm_num) x
  have ha: DifferentiableAt ℝ (axis e) x :=
    (axis_contDiff e (n:=1)).differentiable (by norm_num) x
  have hyq : DifferentiableAt ℝ (fun z=>y (radiusSq e z)) x := hy.comp x hq
  have hkq : DifferentiableAt ℝ (fun z=>k (radiusSq e z)) x := hk.comp x hq
  have hs : DifferentiableAt ℝ (fun z=>axis e z*k (radiusSq e z)) x := ha.mul hkq
  have hhs : DifferentiableAt ℝ (fun z=>h (axis e z*k (radiusSq e z))) x := hh.comp x hs
  change gradient (fun z=>y (radiusSq e z)*h (axis e z*k (radiusSq e z))) x=_
  rw [gradient_mul hyq hhs,gradient_comp hy hq,gradient_comp (f:=fun z:E=>axis e z*k (radiusSq e z)) hh hs,
    gradient_mul ha hkq,gradient_comp hk hq,gradient_radiusSq,gradient_axis]
  simp only [smul_smul]
  module

lemma laplacian_lift {e x:E} (he:‖e‖=1) {y k h:ℝ→ℝ}
    (hy:ContDiffAt ℝ 2 y (radiusSq e x)) (hk:ContDiffAt ℝ 2 k (radiusSq e x))
    (hh:ContDiffAt ℝ 2 h (axis e x*k (radiusSq e x))) :
    Δ (lift e y k h) x =
      y (radiusSq e x)*deriv (deriv h) (axis e x*k (radiusSq e x))*
        ((k (radiusSq e x))^2+4*radiusSq e x*(axis e x)^2*(deriv k (radiusSq e x))^2)+
      deriv h (axis e x*k (radiusSq e x))*
        (axis e x*y (radiusSq e x)*(4*radiusSq e x*deriv (deriv k) (radiusSq e x)+
          2*((Module.finrank ℝ E:ℝ)-1)*deriv k (radiusSq e x))+
          8*radiusSq e x*axis e x*deriv y (radiusSq e x)*deriv k (radiusSq e x))+
      h (axis e x*k (radiusSq e x))*(4*radiusSq e x*deriv (deriv y) (radiusSq e x)+
        2*((Module.finrank ℝ E:ℝ)-1)*deriv y (radiusSq e x)) := by
  let q := radiusSq e
  let a := axis e
  let Y := fun z=>y (q z)
  let K := fun z=>k (q z)
  let s := fun z=>a z*K z
  have hq : ContDiffAt ℝ 2 q x := (radiusSq_contDiff e).contDiffAt
  have ha : ContDiffAt ℝ 2 a x := (axis_contDiff e).contDiffAt
  have hY : ContDiffAt ℝ 2 Y x := hy.comp x hq
  have hK : ContDiffAt ℝ 2 K x := hk.comp x hq
  have hs : ContDiffAt ℝ 2 s x := ha.mul hK
  have gY : gradient Y x=deriv y (q x) • ((2:ℝ) • transverse e x) := by
    rw [gradient_comp (hy.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x]
  have gK : gradient K x=deriv k (q x) • ((2:ℝ) • transverse e x) := by
    rw [gradient_comp (hk.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x]
  have gs : gradient s x=K x • e+(a x*deriv k (q x)*2) • transverse e x := by
    rw [gradient_mul (ha.differentiableAt (by norm_num)) (hK.differentiableAt (by norm_num)),gK]
    rw [show gradient a x=e from gradient_axis e x]
    simp [smul_smul,mul_assoc]
  have gn : ‖gradient q x‖^2=4*q x := by
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x,norm_smul,mul_pow,
      Real.norm_eq_abs,transverse_sq e x he]
    norm_num [q]
  have gort : inner ℝ e (transverse e x)=0 := by rw [real_inner_comm,transverse_inner e x he]
  have gsn : ‖gradient s x‖^2=(K x)^2+4*q x*(a x)^2*(deriv k (q x))^2 := by
    rw [gs,norm_add_sq_real]
    simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,he,mul_one,
      real_inner_smul_left,real_inner_smul_right,gort,mul_zero,add_zero,transverse_sq e x he]
    dsimp [q]; ring
  have gaK : inner ℝ (gradient a x) (gradient K x)=0 := by
    rw [show gradient a x=e from gradient_axis e x,gK]
    simp [real_inner_smul_right,gort]
  have gYs : inner ℝ (gradient Y x) (gradient s x)=4*q x*a x*deriv y (q x)*deriv k (q x) := by
    rw [gY,gs]
    simp only [inner_add_right,real_inner_smul_left,real_inner_smul_right,
      transverse_inner e x he,mul_zero,zero_add,real_inner_self_eq_norm_sq,transverse_sq e x he]
    dsimp [q]; ring
  have lY : Δ Y x=deriv (deriv y) (q x)*(4*q x)+deriv y (q x)*(2*((Module.finrank ℝ E:ℝ)-1)) := by
    rw [laplacian_comp hy hq,gn,show Δ q x=2*((Module.finrank ℝ E:ℝ)-1) from laplacian_radiusSq e x he]
  have lK : Δ K x=deriv (deriv k) (q x)*(4*q x)+deriv k (q x)*(2*((Module.finrank ℝ E:ℝ)-1)) := by
    rw [laplacian_comp hk hq,gn,show Δ q x=2*((Module.finrank ℝ E:ℝ)-1) from laplacian_radiusSq e x he]
  have ls : Δ s x=a x*Δ K x := by
    rw [laplacian_mul ha hK,show Δ a x=0 from laplacian_axis e x,gaK]
    ring
  have gH : gradient (fun z=>h (s z)) x=deriv h (s x) • gradient s x :=
    gradient_comp (hh.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num))
  change Δ (fun z=>Y z*h (s z)) x = _
  have hH : ContDiffAt ℝ 2 (fun z=>h (s z)) x := hh.comp x hs
  rw [laplacian_mul hY hH,laplacian_comp (f:=s) hh hs,gH,
    real_inner_smul_right,gYs,gsn,ls,lK,lY]
  dsimp [Y,K,s,a,q]
  ring
end Bernoulli.Cylindrical

end
end

end OAI

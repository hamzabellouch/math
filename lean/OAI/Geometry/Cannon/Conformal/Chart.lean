import Mathlib
import OAI.Geometry.Cannon.Conformal.SphereTile
import OAI.Geometry.Cannon.Conformal.Round

namespace OAI

section
noncomputable section
namespace CannonStereo
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereo_inner {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    inner ℝ (stereoInvFunAux v x) (stereoInvFunAux v y) =
      (16*inner ℝ (x:E) (y:E)+(‖x‖^2-4)*(‖y‖^2-4)) /
        ((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.2
  have hy := Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.2
  have hy' : inner ℝ v (y:E)=0 := by rw [real_inner_comm,hy]
  simp only [stereoInvFunAux_apply,inner_smul_left,inner_smul_right,
    inner_add_left,inner_add_right,conj_trivial,hx,hy',real_inner_self_eq_norm_sq,hv]
  simp only [div_eq_mul_inv,mul_inv_rev,Submodule.norm_coe]

  ring

lemma stereo_dist_sq {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    (dist (stereoInvFun hv x) (stereoInvFun hv y))^2 =
      16*(dist x y)^2/((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv x.2)
  have hy := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv y.2)
  change (dist (stereoInvFunAux v x) (stereoInvFunAux v y))^2=_
  rw [dist_eq_norm,norm_sub_sq_real,hx,hy,stereo_inner hv]
  rw [dist_eq_norm,norm_sub_sq_real]
  have hp : ‖x‖^2+4 ≠ 0 := by positivity
  have hq : ‖y‖^2+4 ≠ 0 := by positivity
  simp only [Submodule.coe_inner]
  field_simp [hp,hq]
  ring

lemma stereo_dist {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    dist (stereoInvFun hv x) (stereoInvFun hv y) =
      4*dist x y/(Real.sqrt (‖x‖^2+4)*Real.sqrt (‖y‖^2+4)) := by
  have hx : 0 < Real.sqrt (‖x‖^2+4) := Real.sqrt_pos.mpr (by positivity)
  have hy : 0 < Real.sqrt (‖y‖^2+4) := Real.sqrt_pos.mpr (by positivity)
  have hh := stereo_dist_sq hv x y
  have he : (4*dist x y/(Real.sqrt (‖x‖^2+4)*Real.sqrt (‖y‖^2+4)))^2 =
      16*(dist x y)^2/((‖x‖^2+4)*(‖y‖^2+4)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    norm_num
  nlinarith [div_nonneg (show 0 ≤ 4*dist x y by positivity) (mul_nonneg hx.le hy.le),
    dist_nonneg (x:=stereoInvFun hv x) (y:=stereoInvFun hv y)]

end CannonStereo

noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma coe_dist_sq (z w : ℂ) : dist (z:Sphere) (w:Sphere)^2=
    16*dist z w^2/((‖z‖^2+4)*(‖w‖^2+4)) := by
  rw [sphere_dist,roundChart_coe,roundChart_coe,CannonStereo.stereo_dist_sq]
  simp only [planeHyperplane.isometry.dist_eq,planeHyperplane.norm_map]

lemma coe_dist_le (z w : ℂ) : dist (z:Sphere) (w:Sphere) ≤ dist z w := by
  have h:=coe_dist_sq z w
  have hden : 0<(‖z‖^2+4)*(‖w‖^2+4):=by positivity
  have hden' : 16≤(‖z‖^2+4)*(‖w‖^2+4):=by nlinarith [sq_nonneg ‖z‖,sq_nonneg ‖w‖,mul_nonneg (sq_nonneg ‖z‖) (sq_nonneg ‖w‖)]
  have hs : dist (z:Sphere) (w:Sphere)^2 ≤ dist z w^2 := by
    rw [h,div_le_iff₀ hden]
    nlinarith [mul_nonneg (sq_nonneg (dist z w)) (show 0≤(‖z‖^2+4)*(‖w‖^2+4)-16 by linarith)]
  nlinarith [dist_nonneg (x:=z) (y:=w),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]

lemma isometry_of_punctured_dist (f : Sphere ≃ₜ Sphere) (p : ℂ)
    (h : ∀ z w : ℂ,z≠p → w≠p → dist (f (z:Sphere)) (f (w:Sphere))=dist (z:Sphere) (w:Sphere)) :
    Isometry f := by
  let S : Set Sphere:=((↑) : ℂ → Sphere) '' {p}ᶜ
  have hd : Dense S:=OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe (dense_compl_singleton p)
  have hx (x : Sphere) (hx : x∈S) : ∀ y,dist (f x) (f y)=dist x y := by
    have he : EqOn (fun y=>dist (f x) (f y)) (fun y=>dist x y) S := by
      rintro y ⟨w,hw,rfl⟩
      obtain ⟨z,hz,rfl⟩:=hx
      exact h z w hz hw
    have he':=he.closure (continuous_const.dist f.continuous) (continuous_const.dist continuous_id)
    rw [hd.closure_eq] at he'
    exact fun _=>he' (mem_univ _)
  apply Isometry.of_dist_eq
  intro x y
  have he : EqOn (fun x=>dist (f x) (f y)) (fun x=>dist x y) S:=fun x hh=>hx x hh y
  have he':=he.closure (f.continuous.dist continuous_const) (continuous_id.dist continuous_const)
  rw [hd.closure_eq] at he'
  exact he' (mem_univ _)

def chartZero : Sphere ≃ₜ Sphere := affine 4 0 (by norm_num)*inversion
def chartOne : Sphere ≃ₜ Sphere := affine 5 (-1) (by norm_num)*inversion*affine (-1) 1 (by norm_num)

lemma chartZero_finite {z : ℂ} (hz : z≠0) : chartZero (z:Sphere)=((4/z:ℂ):Sphere) := by
  change affine 4 0 _ (inv (z:Sphere))=_
  rw [inv_coe hz,affine_coe]
  simp [div_eq_mul_inv]

lemma chartOne_finite {z : ℂ} (hz : z≠1) : chartOne (z:Sphere)=(((z+4)/(1-z):ℂ):Sphere) := by
  have hden : -(1:ℂ)*z+1≠0:=by intro e; apply hz; linear_combination -e
  change affine 5 (-1) _ (inv (affine (-1) 1 _ (z:Sphere)))=_
  rw [affine_coe,inv_coe hden,affine_coe]
  congr 1
  have hn : (1:ℂ)-z≠0:=sub_ne_zero.mpr hz.symm
  simp only [neg_one_mul,neg_add_eq_sub]
  field_simp
  ring

lemma chartOne_norm_id (z : ℂ) : ‖z+4‖^2+4*‖1-z‖^2=5*(‖z‖^2+4) := by
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,
    Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im]
  norm_num
  ring

theorem chartZero_isometry : Isometry chartZero := by
  apply isometry_of_punctured_dist _ 0
  intro z w hz hw
  rw [chartZero_finite hz,chartZero_finite hw]
  have hnz : ‖z‖≠0:=norm_ne_zero_iff.mpr hz
  have hnw : ‖w‖≠0:=norm_ne_zero_iff.mpr hw
  have he : (4:ℂ)/z-4/w= -4*(z-w)/(z*w):=by field_simp; ring
  have hs : dist ((4/z:ℂ):Sphere) ((4/w:ℂ):Sphere)^2=dist (z:Sphere) (w:Sphere)^2 := by
    rw [coe_dist_sq,coe_dist_sq]
    simp only [dist_eq_norm,he,norm_div,norm_mul,norm_neg,Complex.norm_ofNat]
    field_simp
    ring
  nlinarith [dist_nonneg (x:=((4/z:ℂ):Sphere)) (y:=((4/w:ℂ):Sphere)),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]

theorem chartOne_isometry : Isometry chartOne := by
  apply isometry_of_punctured_dist _ 1
  intro z w hz hw
  rw [chartOne_finite hz,chartOne_finite hw]
  have hz' : (1:ℂ)-z≠0:=sub_ne_zero.mpr hz.symm
  have hw' : (1:ℂ)-w≠0:=sub_ne_zero.mpr hw.symm
  have hnz : ‖(1:ℂ)-z‖≠0:=norm_ne_zero_iff.mpr hz'
  have hnw : ‖(1:ℂ)-w‖≠0:=norm_ne_zero_iff.mpr hw'
  have he : (z+4)/(1-z)-(w+4)/(1-w)=5*(z-w)/((1-z)*(1-w)):=by field_simp; ring
  have hs : dist (((z+4)/(1-z):ℂ):Sphere) (((w+4)/(1-w):ℂ):Sphere)^2=dist (z:Sphere) (w:Sphere)^2 := by
    rw [coe_dist_sq,coe_dist_sq]
    simp only [dist_eq_norm,he,norm_div,norm_mul,Complex.norm_ofNat]
    have hiz:=chartOne_norm_id z
    have hiw:=chartOne_norm_id w
    field_simp
    have hiz' : ‖z+4‖^2+‖1-z‖^2*4=5*(‖z‖^2+4):=by nlinarith [hiz]
    have hiw' : ‖w+4‖^2+‖1-w‖^2*4=5*(‖w‖^2+4):=by nlinarith [hiw]
    rw [hiz',hiw']
    ring
  nlinarith [dist_nonneg (x:=(((z+4)/(1-z):ℂ):Sphere)) (y:=(((w+4)/(1-w):ℂ):Sphere)),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]
end CannonMobius

end
end
end

end OAI

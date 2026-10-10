import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BondiBalance

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Finset CKSInducedSphere
open scoped RealInnerProductSpace ContDiff

def metric (b : E → ℝ) (x : E) (i j : Ix) : ℝ :=
  (if i = j then 1 else 0) + b x * normal x i * normal x j

def energyIntegrand (b : E → ℝ) (x : E) : ℝ :=
  ∑ i : Ix, (∑ j : Ix, (pd j (fun y => metric b y i j) x -
    pd i (fun y => metric b y j j) x)) * normal x i

lemma pd_norm {x : E} (hx : x ≠ 0) (i : Ix) :
    pd i (fun y : E => ‖y‖) x = normal x i := by
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  have hsq : pd i (fun y : E => ‖y‖^2) x = 2*‖x‖*pd i (fun y : E => ‖y‖) x := by
    rw [pd, (hn.hasFDerivAt.pow 2).fderiv]
    simp [pd]
  have hsq' : pd i (fun y : E => ‖y‖^2) x = 2*x i := by
    rw [pd,fderiv_norm_sq_apply]
    simp [smul_apply, innerSL_apply_apply,e,EuclideanSpace.inner_single_right]
  unfold normal
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  nlinarith

lemma normal_diff {x : E} (hx : x ≠ 0) (i : Ix) :
    DifferentiableAt ℝ (fun y => normal y i) x := by
  have hi : DifferentiableAt ℝ (fun y : E => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).differentiableAt
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  simpa only [normal,div_eq_mul_inv,Pi.inv_apply] using hi.fun_mul (hn.inv (norm_ne_zero_iff.mpr hx))

lemma pd_normal {x : E} (hx : x ≠ 0) (i j : Ix) :
    pd j (fun y => normal y i) x =
      ((if i = j then 1 else 0) - normal x i * normal x j) / ‖x‖ := by
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  have hi : DifferentiableAt ℝ (fun y : E => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).differentiableAt
  have hh := ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn.hasFDerivAt).fderiv
  have hInv : pd j (fun y : E => (‖y‖)⁻¹) x = -(‖x‖^2)⁻¹ * normal x j := by
    unfold pd
    erw [hh]
    simp only [smul_apply,smul_eq_mul]
    change -((‖x‖^2)⁻¹) * pd j (fun y : E => ‖y‖) x = _
    rw [pd_norm hx]
  unfold normal
  simp_rw [div_eq_mul_inv]
  erw [pd_mul hi (hn.inv (norm_ne_zero_iff.mpr hx)),pd_coordinate,hInv]
  unfold normal
  simp only [eq_comm (a := i) (b := j),Pi.inv_apply]
  field_simp [norm_ne_zero_iff.mpr hx]
  split_ifs <;> ring

lemma normal_sq {x : E} (hx : x ≠ 0) : ∑ i : Ix, normal x i ^ 2 = 1 := by
  simp only [normal,div_pow,← Finset.sum_div]
  have hs : (∑ i : Ix, x i ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  rw [hs]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_metric {b : E → ℝ} {x : E} (hb : DifferentiableAt ℝ b x) (hx : x ≠ 0)
    (k i j : Ix) :
    pd k (fun y => metric b y i j) x = pd k b x * normal x i * normal x j +
      b x * (((if i = k then 1 else 0)-normal x i*normal x k)/‖x‖) * normal x j +
      b x * normal x i * (((if j = k then 1 else 0)-normal x j*normal x k)/‖x‖) := by
  have hi := normal_diff hx i
  have hj := normal_diff hx j
  unfold metric
  rw [pd, fderiv_const_add, fderiv_fun_mul (hb.fun_mul hi) hj,
    fderiv_fun_mul hb hi]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change b x * normal x i * pd k (fun y => normal y j) x +
    normal x j * (b x * pd k (fun y => normal y i) x + normal x i * pd k b x) = _
  rw [pd_normal hx,pd_normal hx]
  ring

lemma contracted_flux (b r : ℝ) (n p : Ix → ℝ) (hn : ∑ i, n i^2 = 1) (hr : r ≠ 0) :
    (∑ i : Ix, (∑ j : Ix, (
      (p j*n i*n j+b*((if i=j then 1 else 0)-n i*n j)/r*n j+
        b*n i*((if j=j then 1 else 0)-n j*n j)/r) -
      (p i*n j*n j+b*((if j=i then 1 else 0)-n j*n i)/r*n j+
        b*n j*((if j=i then 1 else 0)-n j*n i)/r))) * n i) = 2*b/r := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at hn ⊢
  norm_num [Ix, Fin.reduceEq] at hn ⊢
  apply (eq_div_iff hr).mpr
  field_simp
  linear_combination 2*b*hn

theorem energyIntegrand_eq {b : E → ℝ} {x : E} (hb : DifferentiableAt ℝ b x) (hx : x ≠ 0) :
    energyIntegrand b x = 2*b x/‖x‖ := by
  unfold energyIntegrand
  simp_rw [pd_metric hb hx]
  simpa only [mul_div_assoc,ite_true] using contracted_flux (b x) ‖x‖ (normal x) (fun i => pd i b x)
    (normal_sq hx) (norm_ne_zero_iff.mpr hx)

end
end CKSADM

end

end OAI

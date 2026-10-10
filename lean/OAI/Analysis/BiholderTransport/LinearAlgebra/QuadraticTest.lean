import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LowerTaylor
import OAI.Analysis.BiholderTransport.Regularity.SecondFderivAdd
import OAI.Analysis.BiholderTransport.Regularity.CenteredQuadratic

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section QuadraticTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma diag_bilinear_c2 (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ 2 (fun h : E => B h h/2) := by
  convert! ((B.contDiff.clm_apply contDiff_id).const_smul (1/2:ℝ)) using 1
  ext h
  simp only [smul_eq_mul,id_eq]
  ring

lemma diag_bilinear_fderiv (B : E →L[ℝ] E →L[ℝ] ℝ) :
    fderiv ℝ (fun h:E => B h h/2) = fun h => (1/2:ℝ) • (B+B.flip) h := by
  funext h
  have H := (B.hasFDerivAt.clm_apply (hasFDerivAt_id h)).const_smul (1/2:ℝ)
  have hfun : ((1/2:ℝ) • (fun y:E => B y (id y)))=(fun y:E => B y y/2) := by
    ext y
    simp only [Pi.smul_apply,smul_eq_mul,id_eq]
    ring
  rw [hfun] at H
  rw [H.fderiv]
  ext d
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.id_apply,id_eq]

lemma diag_bilinear_second (B : E →L[ℝ] E →L[ℝ] ℝ) (d : E) :
    fderiv ℝ (fderiv ℝ (fun h:E => B h h/2)) 0 d d=B d d := by
  rw [diag_bilinear_fderiv]
  change fderiv ℝ ((1/2:ℝ) • (B+B.flip)) 0 d d=B d d
  rw [ContinuousLinearMap.fderiv]
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

lemma HasLowerSecondTaylor.exists_smooth_minorant {f : E → ℝ}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor f l B) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → ℝ, ContDiffAt ℝ 2 q 0 ∧ q 0=f 0 ∧ fderiv ℝ q 0=l ∧
      (∀ᶠ h in 𝓝 0,q h≤f h) ∧
      ∀ d:E,fderiv ℝ (fderiv ℝ q) 0 d d = B d d-ε*‖d‖^2 := by
  let q : E → ℝ := fun h => f 0+l h+B h h/2-ε*(‖h‖^2/2)
  have hB : ContDiffAt ℝ 2 (fun h:E => B h h/2) 0 := (diag_bilinear_c2 B).contDiffAt
  have hn : ContDiffAt ℝ 2 (fun h:E => ‖h‖^2/2) 0 := by
    simpa only [sub_zero] using (centered_half_norm_sq_c2 (0:E)).contDiffAt
  have hc : ContDiffAt ℝ 2 (fun h:E => f 0+l h) 0 := contDiffAt_const.add l.contDiff.contDiffAt
  refine ⟨q,(hc.add hB).sub (contDiffAt_const.mul hn),by simp [q],?_,?_,?_⟩
  · rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      fderiv_fun_sub ((hc.add hB).differentiableAt (by norm_num))
        ((contDiffAt_const.mul hn).differentiableAt (by norm_num)),
      fderiv_fun_add (hc.differentiableAt (by norm_num)) (hB.differentiableAt (by norm_num)),
      (l.hasFDerivAt.const_add (f 0)).fderiv,diag_bilinear_fderiv]
    have Hn := ((half_norm_sq_hasFDerivAt (0:E)).const_mul ε).fderiv
    rw [Hn]
    simp only [map_zero,smul_zero,add_zero,sub_zero]

  · filter_upwards [hf (ε/2) (by positivity)] with h hh
    dsimp only [q]
    convert! hh using 1
    ring
  · intro d
    rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      second_fderiv_sub (hc.add hB) (contDiffAt_const.mul hn),
      second_fderiv_add_eq hc hB,add_apply,add_apply,second_fderiv_const_mul,diag_bilinear_second,
      half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq]
    have hlin : fderiv ℝ (fun h:E => f 0+l h)=fun _ => l := by
      funext h
      exact (l.hasFDerivAt.const_add (f 0)).fderiv
    rw [hlin,(hasFDerivAt_const l (0:E)).fderiv]
    simp only [zero_apply,zero_add]

end QuadraticTest
end WeakMTWTransport

end

end

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LowerTaylor
import OAI.Analysis.BiholderTransport.Calculus.LowerTaylorComposition
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma lower_jet_diffeomorphism_bound
    {f:E → F} {g:F → E} {p:E} {A:E →L[ℝ] F} {J:F →L[ℝ] E}
    (hf:HasFDerivAt f A p) (hg:HasFDerivAt g J (f p))
    (hgf:(fun x=>g (f x)) =ᶠ[𝓝 p] id)
    (hfg:(fun y=>f (g y)) =ᶠ[𝓝 (f p)] id)
    {v:F → ℝ} {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hjet:HasLowerSecondTaylor (fun d=>v (f (p+d))) 0 B)
    (hB:∀ d,0 ≤ B d d)
    {C:ℝ} (hC:0 ≤ C)
    (hbound:∀ H:F →L[ℝ] F →L[ℝ] ℝ,
      (∀ w,0 ≤ H w w) → HasLowerSecondTaylor (fun w=>v (f p+w)) 0 H → ∀ w,H w w ≤ C*‖w‖^2) :
    ∀ d,B d d ≤ C*‖A‖^2*‖d‖^2 := by
  have hg0:g (f p)=p := hgf.eq_of_nhds
  have ha:HasFDerivAt (fun w=>g (f p+w)-p) J 0 := by
    have hg' : HasFDerivAt g J (f p+id (0:F)) := by simpa only [id_eq,add_zero] using hg
    have H:=hg'.comp 0 ((hasFDerivAt_id (0:F)).const_add (f p))
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_apply,id_eq] using H.sub_const p
  have ha0:g (f p+0)-p=0 := by rw [add_zero,hg0,sub_self]
  have H:=hjet.comp_stationary ha ha0
  have heq:(fun w=>v (f (p+(g (f p+w)-p)))) =ᶠ[𝓝 (0:F)]
      (fun w=>v (f p+w)) := by
    have ht:Tendsto (fun w:F=>f p+w) (𝓝 0) (𝓝 (f p)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add (tendsto_id : Tendsto (fun w:F=>w) (𝓝 0) (𝓝 0)) :
          Tendsto (fun w:F=>f p+w) (𝓝 0) (𝓝 (f p+0)))
    filter_upwards [ht.eventually hfg] with w hw
    have hp:p+(g (f p+w)-p)=g (f p+w) := by abel
    rw [hp,hw,id_eq]
  have HE:=H.mono heq.eq_of_nhds heq.le
  have hJA:J.comp A=ContinuousLinearMap.id ℝ E := by
    have HD:= (hg.comp p hf).congr_of_eventuallyEq hgf.symm
    exact HD.unique (hasFDerivAt_id p)
  intro d
  have HH:=hbound (pullBilinear B J) (fun w=>by simpa only [pullBilinear_apply] using hB (J w)) HE (A d)
  have hid:J (A d)=d := by simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun T:E →L[ℝ] E=>T d) hJA
  rw [pullBilinear_apply,hid] at HH
  have hn:=A.le_opNorm d
  have hsq:‖A d‖^2 ≤ ‖A‖^2*‖d‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  exact HH.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsq hC])

end WeakMTWTransport

end

end OAI

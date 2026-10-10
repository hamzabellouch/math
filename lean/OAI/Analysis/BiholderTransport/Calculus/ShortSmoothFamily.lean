import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives

namespace OAI



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma smooth_family_local_inverse {Z : P×E → E} {p : P} {x : E}
    (hZ : ContDiffAt ℝ ∞ Z (p,x))
    (hDx : HasFDerivAt (fun y => Z (p,y)) (ContinuousLinearMap.id ℝ E) x) :
    ∃ B : P×E → E, ContDiffAt ℝ ∞ B (p,Z (p,x)) ∧ B (p,Z (p,x))=x ∧
      (∀ᶠ q in 𝓝 (p,Z (p,x)),Z (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 (p,x), B (q.1,Z q)=q.2) ∧
      (∀ᶠ q : (P×E)×E in 𝓝 ((p,Z (p,x)),x),
        Z (q.1.1,q.2)=q.1.2 ↔ B q.1=q.2) := by
  let F : (P×E)×E → E := fun q => Z (q.1.1,q.2)-q.1.2
  have hF : ContDiffAt ℝ ∞ F ((p,Z (p,x)),x) :=
    (hZ.comp (f := fun q : (P×E)×E => (q.1.1,q.2)) ((p,Z (p,x)),x)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hFy : HasFDerivAt (fun y => F ((p,Z (p,x)),y)) (ContinuousLinearMap.id ℝ E) x :=
    hDx.sub_const (Z (p,x))
  have hpart : fderiv ℝ F ((p,Z (p,x)),x) ∘L inr ℝ (P×E) E=ContinuousLinearMap.id ℝ E := by
    have H := (hF.differentiableAt (by simp)).hasFDerivAt.comp
      (f := fun y => ((p,Z (p,x)),y)) x
      ((hasFDerivAt_const (p,Z (p,x)) x).prodMk (hasFDerivAt_id x))
    exact H.unique hFy
  have hi : (fderiv ℝ F ((p,Z (p,x)),x) ∘L inr ℝ (P×E) E).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  let B := hF.implicitFunction (by simp) hi
  have hB : ContDiffAt ℝ ∞ B (p,Z (p,x)) := hF.contDiffAt_implicitFunction (by simp) hi
  have hBx : B (p,Z (p,x))=x := hF.implicitFunction_apply_self (by simp) hi
  have hiff : ∀ᶠ q : (P×E)×E in 𝓝 ((p,Z (p,x)),x),
      Z (q.1.1,q.2)=q.1.2 ↔ B q.1=q.2 := by
    filter_upwards [hF.eventually_apply_eq_iff_implicitFunction (by simp) hi] with q hq
    simpa only [F,sub_self,sub_eq_zero] using hq
  refine ⟨B,hB,hBx,?_,?_,hiff⟩
  · filter_upwards [hF.eventually_apply_implicitFunction (by simp) hi] with q hq
    simpa only [F,sub_self,sub_eq_zero] using hq
  · have hc : ContinuousAt (fun q : P×E => ((q.1,Z q),q.2)) (p,x) :=
      (continuousAt_fst.prodMk hZ.continuousAt).prodMk continuousAt_snd
    filter_upwards [hc.eventually hiff] with q hq
    exact hq.mp rfl

lemma parametric_smooth_short_action {Z : (P×ℝ)×E → E} {ψ K : P×E → ℝ}
    {p : P} {x : E} (hZ : ContDiffAt ℝ ∞ Z ((p,0),x))
    (hZ0 : ∀ᶠ y in 𝓝 x,Z ((p,0),y)=y)
    (hψ : ContDiffAt ℝ ∞ ψ (p,x)) (hK : ContDiffAt ℝ ∞ K (p,x)) :
    ∃ (B : (P×ℝ)×E → E) (U : (P×ℝ)×E → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),Z (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,Z q)=q.2) ∧
      (∀ q,U q=ψ (q.1.1,B q)+q.1.2*K (q.1.1,B q)) ∧
      Tendsto (fun q : (P×ℝ)×E => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  have hDx : HasFDerivAt (fun y => Z ((p,0),y)) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).congr_of_eventuallyEq hZ0
  obtain ⟨B,hB,hBx,hBZ,hZB,hiff⟩ := smooth_family_local_inverse hZ hDx
  have hx0 := hZ0.self_of_nhds
  rw [hx0] at hB hBx hBZ hiff
  let U : (P×ℝ)×E → ℝ := fun q => ψ (q.1.1,B q)+q.1.2*K (q.1.1,B q)
  have hbq : ContDiffAt ℝ ∞ (fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) :=
    contDiffAt_fst.fst.prodMk hB
  have hU : ContDiffAt ℝ ∞ U ((p,0),x) := by
    have hpψ : ContDiffAt ℝ ∞ ψ (p,B ((p,0),x)) := by rwa [hBx]
    have hpK : ContDiffAt ℝ ∞ K (p,B ((p,0),x)) := by rwa [hBx]
    exact (hpψ.comp (f := fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) hbq).add
      (contDiffAt_fst.snd.mul (hpK.comp (f := fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) hbq))
  have hU0 : (fun y => U ((p,0),y))=ᶠ[𝓝 x] (fun y => ψ (p,y)) := by
    have hc : ContinuousAt (fun y : E => ((p,(0:ℝ)),y)) x :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.eventually hZB,hZ0] with y hy hz
    rw [hz] at hy
    simp only [U,hy,zero_mul,add_zero]
  refine ⟨B,U,hB,hU,hBx,hBZ,hZB,fun _ => rfl,?_⟩
  have H := (ContDiffAt.partial_snd_fderiv_two (f := fun q y => U (q,y)) hU).continuousAt.tendsto
  rwa [hU0.fderiv.fderiv_eq] at H

end WeakMTWTransport

end

end OAI

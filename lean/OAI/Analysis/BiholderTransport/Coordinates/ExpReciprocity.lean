import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalLogMixed
import OAI.Analysis.BiholderTransport.Coordinates.LocalInverseCalculus
import OAI.Analysis.BiholderTransport.Regularity.ReciprocalInverses

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_reciprocal_normal_exp_coordinates {x y : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hp : p∈injectivityDomain x) (hq : q∈injectivityDomain y)
    (hpx : riemannianExp x p=y) (hqy : riemannianExp y q=x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ L p ∧ ContDiffAt ℝ ∞ R q ∧ L p=0 ∧ R q=0 ∧
      (∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v) ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      ∀ v w, inner ℝ (fderiv ℝ L p v) w=inner ℝ v (fderiv ℝ R q w) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨X,hX,hXp,hXi,hXl⟩ := exists_smooth_two_sided_fiber_log hp
  obtain ⟨Y,hY,hYq,hYi,hYl⟩ := exists_smooth_two_sided_fiber_log hq
  obtain ⟨Nx,hNx,hNx0,hNxi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) x)
  obtain ⟨Ny,hNy,hNy0,hNyi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) y)
  rw [hpx] at hX hXp hXi
  rw [hqy] at hY hYq hYi
  simp only [riemannianExp_zero] at hNx hNx0 hNxi hNy hNy0 hNyi
  let e : W → V := fun w => X (riemannianExp y w)
  let f : V → W := fun v => Y (riemannianExp x v)
  let L : V → W := fun v => Ny (riemannianExp x v)
  let R : W → V := fun w => Nx (riemannianExp y w)
  have he : ContDiffAt ℝ ∞ e 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ X (riemannianExp y 0) from
      by simpa only [riemannianExp_zero] using hX).comp 0 (contMDiff_riemannianExp_fiber y 0)).contDiffAt
  have hf : ContDiffAt ℝ ∞ f 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,W) ∞ Y (riemannianExp x 0) from
      by simpa only [riemannianExp_zero] using hY).comp 0 (contMDiff_riemannianExp_fiber x 0)).contDiffAt
  have hL : ContDiffAt ℝ ∞ L p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,W) ∞ Ny (riemannianExp x p) from
      by simpa only [hpx] using hNy).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hR : ContDiffAt ℝ ∞ R q :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ Nx (riemannianExp y q) from
      by simpa only [hqy] using hNx).comp q (contMDiff_riemannianExp_fiber y q)).contDiffAt
  have he0 : e 0=p := by dsimp [e]; rw [riemannianExp_zero,hXp]
  have hf0 : f 0=q := by dsimp [f]; rw [riemannianExp_zero,hYq]
  have hLp : L p=0 := by dsimp [L]; rw [hpx,hNy0]
  have hRq : R q=0 := by dsimp [R]; rw [hqy,hNx0]
  have hei : ∀ᶠ w in 𝓝 (0:W), riemannianExp x (e w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) (0:W) from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hXi)
  have hfi : ∀ᶠ v in 𝓝 (0:V), riemannianExp y (f v)=riemannianExp x v :=
    (show ContinuousAt (riemannianExp x) (0:V) from (continuous_riemannianExp x).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hYi)
  have hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v :=
    (show ContinuousAt (riemannianExp x) p from (continuous_riemannianExp x).continuousAt).eventually
      (by simpa only [hpx] using hNyi)
  have hRi : ∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) q from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [hqy] using hNxi)
  have heL : (fun v => e (L v)) =ᶠ[𝓝 p] (fun v => v) := by
    filter_upwards [hLi,hXl] with v hvi hvl
    change X (riemannianExp y (L v))=v
    rw [hvi]
    exact hvl
  have hfR : (fun w => f (R w)) =ᶠ[𝓝 q] (fun w => w) := by
    filter_upwards [hRi,hYl] with w hwi hwl
    change Y (riemannianExp x (R w))=w
    rw [hwi]
    exact hwl
  have hAL : ∀ v:V, fderiv ℝ e 0 (fderiv ℝ L p v)=v := by
    intro v
    have H := local_inverse_derivative (by simpa only [hLp] using he.differentiableAt (by simp))
      (hL.differentiableAt (by simp)) heL v
    simpa only [hLp] using H
  have hBR : ∀ w:W, fderiv ℝ f 0 (fderiv ℝ R q w)=w := by
    intro w
    have H := local_inverse_derivative (by simpa only [hRq] using hf.differentiableAt (by simp))
      (hR.differentiableAt (by simp)) hfR w
    simpa only [hRq] using H
  refine ⟨L,R,hL,hR,hLp,hRq,hLi,hRi,?_⟩
  exact reciprocal_inverses (normal_log_derivatives_adjoint he hf (he0 ▸ hp) (hf0 ▸ hq) hei hfi) hAL hBR

end WeakMTWTransport

end

end OAI

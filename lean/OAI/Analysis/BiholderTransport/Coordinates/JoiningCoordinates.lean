import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiberLog

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

lemma exists_smooth_joining_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hh : h≠0) (hp : h • p∈injectivityDomain x) :
    let z := riemannianExp x (h • p)
    ∃ g : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) z,
      ContDiffAt ℝ ∞ g p ∧ g p=0 ∧
      (∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b)) ∧
      Function.Injective (fderiv ℝ g p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z := riemannianExp x (h • p)
  let W := TangentSpace 𝓘(ℝ,Model n) z
  obtain ⟨L,hL,hL0,hLi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) z)
  simp only [riemannianExp_zero] at hL hL0 hLi
  let s : V →L[ℝ] V := h • ContinuousLinearMap.id ℝ V
  have hc : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞
      (fun b : V => riemannianExp x (h • b)) p :=
    (contMDiff_riemannianExp_fiber x (h • p)).comp p s.contDiff.contMDiff.contMDiffAt
  let g : V → W := fun b => L (riemannianExp x (h • b))
  have hg : ContDiffAt ℝ ∞ g p := (hL.comp p hc).contDiffAt
  have hg0 : g p=0 := hL0
  have hgi : ∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b) :=
    hc.continuousAt.eventually hLi
  refine ⟨g,hg,hg0,hgi,?_⟩
  let cx : V → Model n := fun v => extChartAt 𝓘(ℝ,Model n) z (riemannianExp x v)
  let cz : W → Model n := fun v => extChartAt 𝓘(ℝ,Model n) z (riemannianExp z v)
  have hcx : ContDiffAt ℝ ∞ cx (h • p) :=
    (contMDiffAt_extChartAt.comp (h • p) (contMDiff_riemannianExp_fiber x (h • p))).contDiffAt
  have hcz : ContDiffAt ℝ ∞ cz 0 := by
    have H := (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) z) (riemannianExp z (0:W)) from by
        simpa only [riemannianExp_zero] using
          (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n)) (x := z))).comp 0
        (contMDiff_riemannianExp_fiber z 0)
    exact H.contDiffAt
  have he : (fun b => cz (g b)) =ᶠ[𝓝 p] (fun b => cx (s b)) :=
    hgi.mono (fun _ hb => congrArg (extChartAt 𝓘(ℝ,Model n) z) hb)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp p (by simpa only [hg0] using hcz.differentiableAt (by simp))
    (hg.differentiableAt (by simp)),fderiv_fun_comp p (f := s) (g := cx)
    (by simpa [s] using hcx.differentiableAt (by simp)) s.differentiableAt,s.fderiv] at hd
  intro v w hvw
  have H := congrArg (fun A : V →L[ℝ] Model n => A v-A w) hd
  simp only [ContinuousLinearMap.comp_apply,hvw,sub_self] at H
  have hi : Function.Injective (fderiv ℝ cx (h • p)) :=
    riemannianExp_interior_nonconjugate hp
  have Hs : s v=s w := hi (by simpa [s] using sub_eq_zero.mp H.symm)
  apply (smul_right_injective V hh)
  simpa [s] using Hs

end WeakMTWTransport

end

end OAI

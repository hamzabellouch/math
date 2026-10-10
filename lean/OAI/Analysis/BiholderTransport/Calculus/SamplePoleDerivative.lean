import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiberLog
import OAI.Analysis.BiholderTransport.Regularity.GraphInverse

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.continuous_hopfPole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Continuous (hopfPole (n := n) t (cTransform v)) := by
  have H := (FiberBundle.continuous_proj (Model n)
    (TangentSpace 𝓘(ℝ,Model n))).comp
      (continuous_subtype_val.comp (hmtw.graphHomeomorph hv ht ht1).symm.continuous)
  exact H.congr (fun z=>hmtw.graphHomeomorph_inverse_pole hv ht ht1 z)

lemma WeakMTW.exists_actual_normal_pole_derivative
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x a c : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hpole : hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p))=x)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
      (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
    ∃ e : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      HasFDerivAt e R p ∧ e p=0 ∧
      ∀ᶠ q in 𝓝 p,riemannianExp x (e q)=
        hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) c
  let P := hopfPole (n := n) t (cTransform v)
  let F : Model n → Model n := fun w=>ψ (P (χ.symm w))
  let z := riemannianExp x (t • p)
  let Z : V → Model n := fun q=>χ (riemannianExp x (t • q))
  let S : V →L[ℝ] V := t • ContinuousLinearMap.id ℝ V
  have hc : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞
      (fun q:V=>riemannianExp x (t • q)) p :=
    (contMDiff_riemannianExp_fiber x (t • p)).comp p S.contDiff.contMDiff.contMDiffAt
  have hZ : ContDiffAt ℝ ∞ Z p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using hz)).comp p hc).contDiffAt
  have hFz : F (Z p)=ψ x := by
    dsimp [F,Z]; rw [χ.left_inv hz]; exact congrArg ψ hpole
  obtain ⟨L,hL,hL0,hLi,hLin⟩ := exists_smooth_chart_fiber_log
    (zero_mem_injectivityDomain (n := n) x) (by simpa only [riemannianExp_zero] using hx)
  simp only [riemannianExp_zero] at hL hL0 hLi hLin
  let e : V → V := fun q=>L (F (Z q))
  have hDZ : DifferentiableAt ℝ (fun q=>F (Z q)) p :=
    (show DifferentiableAt ℝ F (Z p) from hD).comp (f := Z) p (hZ.differentiableAt (by simp))
  have hDe : DifferentiableAt ℝ e p :=
    (show DifferentiableAt ℝ L (F (Z p)) from hFz ▸ hL.differentiableAt (by simp)).comp p hDZ
  refine ⟨e,fderiv ℝ e p,hDe.hasFDerivAt,?_,?_⟩
  · dsimp [e]; rw [hFz]; exact hL0
  have hexp : ContinuousAt (fun q:V=>riemannianExp x (t • q)) p := hc.continuousAt
  have hP : ContinuousAt (fun q:V=>P (riemannianExp x (t • q))) p :=
    (hmtw.continuous_hopfPole hv ht ht1).continuousAt.comp hexp
  have hcZ : ∀ᶠ q in 𝓝 p,riemannianExp x (t • q)∈χ.source :=
    hexp.eventually ((isOpen_extChartAt_source a).mem_nhds hz)
  have hcP : ∀ᶠ q in 𝓝 p,P (riemannianExp x (t • q))∈ψ.source :=
    hP.eventually (show ψ.source∈𝓝 (P (riemannianExp x (t • p))) from by
      change ψ.source∈𝓝 (hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p)))
      rw [hpole]; exact (isOpen_extChartAt_source c).mem_nhds hx)
  have hlog : ∀ᶠ q in 𝓝 p,riemannianExp x (L (F (Z q)))=ψ.symm (F (Z q)) :=
    hDZ.continuousAt.eventually (hFz ▸ hLi)
  filter_upwards [hcZ,hcP,hlog] with q hq hpq hlq
  change riemannianExp x (L (F (Z q)))=P (riemannianExp x (t • q))
  rw [hlq]
  dsimp [F,Z]
  rw [χ.left_inv hq,ψ.left_inv hpq]

end WeakMTWTransport

end

end OAI

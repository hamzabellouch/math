import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.StationaryPullback

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

lemma shifted_exp_time (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (h T : ℝ) :
    riemannianExp (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      ((T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)=
      riemannianExp x (T • p) := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale (T-h) (sprayFlow h ⟨x,p⟩))).1=_
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel,riemannianExp_smul]
  rfl

lemma fixedJoinAction_joint_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (TangentSpace 𝓘(ℝ,Model n) x ×
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x)) =>
      fixedJoinAction x h q.1 q.2.1 q.2.2) (T,(p,(0,p))) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let a : ℝ × (V×(V×V)) := (T,(p,(0,p)))
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x q.2.2.1) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.2.2.1) a from by fun_prop).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (h • q.2.2.2)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => h • q.2.2.2) a from by fun_prop).contMDiffAt
  have hw : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (q.1 • q.2.1)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.1 • q.2.1) a from by fun_prop).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (h • p)) := by
    simpa only [riemannianExp_zero] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (h • p),riemannianExp x (T • p)) := by
    dsimp only at hc₂
    rw [shifted_exp_time] at hc₂
    simpa only [riemannianExp_smul] using hc₂
  exact ((hc₁'.comp a (hu.prodMk hv)).contDiffAt.div_const h).add
    (((hc₂'.comp a (hv.prodMk hw)).contDiffAt).div
      (contDiffAt_fst.sub contDiffAt_const) (sub_ne_zero.mpr hTh))

lemma fixedJoinAction_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  exact (fixedJoinAction_joint_contDiffAt hTh hleft hright).comp (0,p)
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))

end WeakMTWTransport

end

end OAI

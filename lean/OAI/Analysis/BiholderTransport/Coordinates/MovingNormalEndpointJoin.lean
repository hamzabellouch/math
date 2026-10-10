import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldLipschitz
import OAI.Analysis.BiholderTransport.Coordinates.NormalEndpointJoin

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

def movingNormalEndpointJoinAction (a c : M)
    (r : ℝ×(Model n×Model n)) (z : Model n×Model n) : ℝ :=
  cost (movingNormal a (r.2.1,0)) (movingNormal a (r.2.1,r.1 • z.2))/r.1+
    cost (movingNormal a (r.2.1,r.1 • z.2)) (movingNormal c (r.2.2,z.1))/(1-r.1)

lemma movingNormalEndpointJoinAction_contDiffAt {a c : M} {b e p : Model n} {h : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (he : e∈(extChartAt 𝓘(ℝ,Model n) c).target)
    (h0 : h≠0) (h1 : h≠1)
    (hend : (extChartAt 𝓘(ℝ,Model n) c).symm e=movingNormal a (b,p))
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (1-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c)) ((h,(b,e)),(0,p)) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let Q := (ℝ×(Model n×Model n))×(Model n×Model n)
  let q : Q := ((h,(b,e)),(0,p))
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,0)) q :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,z.1.1 • z.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,h • p)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk (contDiffAt_fst.fst.smul contDiffAt_snd.snd)).contMDiffAt
  have hC : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal c (z.1.2.2,z.2.1)) q :=
    (movingNormal_contMDiffAt (q := (e,0)) he).comp q
      (contDiffAt_fst.snd.snd.prodMk contDiffAt_snd.fst).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • L p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-h) • (sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,0),movingNormal a (b,h • p)) := by
    simpa only [movingNormal_eq hb,map_zero,riemannianExp_zero,map_smul] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,h • p),movingNormal c (e,0)) := by
    dsimp only at hc₂
    rw [shifted_exp_endpoint] at hc₂
    simp only [movingNormal_eq he,map_zero,riemannianExp_zero,hend]
    simpa only [movingNormal_eq hb,map_smul,riemannianExp_smul] using hc₂
  exact ((hc₁'.comp q (hA.prodMk hB)).contDiffAt.div contDiffAt_fst.fst h0).add
    ((hc₂'.comp q (hB.prodMk hC)).contDiffAt.div
      (contDiffAt_const.sub contDiffAt_fst.fst) (sub_ne_zero.mpr h1.symm))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingNormalEndpointJoinAction_trivialization {a c x y : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) c).source) (h : ℝ)
    (u : TangentSpace 𝓘(ℝ,Model n) y) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormalEndpointJoinAction a c
      (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y u,
       (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x v)=
      normalEndpointJoinAction x y h (u,v) := by
  dsimp only [movingNormalEndpointJoinAction,normalEndpointJoinAction]
  rw [← map_zero ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x),
    ←map_smul,movingNormal_trivialization_exp hx,movingNormal_trivialization_exp hx,
    movingNormal_trivialization_exp hy,riemannianExp_zero]

end WeakMTWTransport

end

end OAI

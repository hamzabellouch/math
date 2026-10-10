import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates3
import OAI.Analysis.BiholderTransport.Coordinates.FixedJoinSmooth

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteProfile (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end WeakMTWTransport

end



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

def movingFixedJoinAction (a : M) (h : ℝ) (q : ℝ×(Model n×Model n)) (z : Model n) : ℝ :=
  cost (movingNormal a (q.2.1,0)) (movingNormal a (q.2.1,h • (q.2.2+z)))/h+
  cost (movingNormal a (q.2.1,h • (q.2.2+z))) (movingNormal a (q.2.1,q.1 • q.2.2))/(q.1-h)

def movingFixedJoinMiddle (a : M) (h : ℝ) (q : ℝ×(Model n×Model n)) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingFixedJoinAction a h q)) 0

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingFixedJoinAction_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (h T : ℝ) (p z : Model n) :
    movingFixedJoinAction a h (T,(b,p)) z=
      fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
      (0,((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)+
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) z)) := by
  simp only [movingFixedJoinAction,fixedJoinAction,movingNormal_eq hb,map_smul,map_add,map_zero]

lemma movingFixedJoinAction_contDiffAt {a : M} {b p : Model n} {h T : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hTh : T≠h)
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (T-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingFixedJoinAction a h)) ((T,(b,p)),0) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let q := ((T,(b,p)),(0 : Model n))
  let Q := (ℝ×(Model n×Model n))×Model n
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,0)) q :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,h • (z.1.2.2+z.2))) q :=
    (movingNormal_contMDiffAt (q := (b,h • (p+0))) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk
        ((contDiffAt_const (c := h)).smul (contDiffAt_fst.snd.snd.add contDiffAt_snd))).contMDiffAt
  have hC : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,z.1.1 • z.1.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,T • p)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk
        (contDiffAt_fst.fst.smul contDiffAt_fst.snd.snd)).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • L p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (T-h) • (sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,0),movingNormal a (b,h • (p+0))) := by
    simpa only [movingNormal_eq hb,map_zero,riemannianExp_zero,add_zero,map_smul] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,h • (p+0)),movingNormal a (b,T • p)) := by
    dsimp only at hc₂
    rw [shifted_exp_time] at hc₂
    simpa only [movingNormal_eq hb,add_zero,map_smul,riemannianExp_smul] using hc₂
  exact ((hc₁'.comp q (hA.prodMk hB)).contDiffAt.div_const h).add
    (((hc₂'.comp q (hB.prodMk hC)).contDiffAt).div
      (contDiffAt_fst.fst.sub contDiffAt_const) (sub_ne_zero.mpr hTh))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingFixedJoinMiddle_contDiffAt {a : M} {h T : ℝ} {b p : Model n}
    (H : ContDiffAt ℝ ∞ (Function.uncurry (movingFixedJoinAction a h)) ((T,(b,p)),0)) :
    ContDiffAt ℝ ∞ (movingFixedJoinMiddle a h) (T,(b,p)) :=
  (ContDiffAt.partial_snd_fderiv_two H).comp (T,(b,p))
    (contDiffAt_id.prodMk contDiffAt_const)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingFixedJoinMiddle_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (h T : ℝ) (p v w : Model n)
    (H : ContDiffAt ℝ 2 (fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))
      (0,((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))) :
    movingFixedJoinMiddle a h (T,(b,p)) v w=
      fixedJoinMiddle ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) v)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) w) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let I := (0 : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x).prod L
  have he : movingFixedJoinAction a h (T,(b,p))=
      (fun z => fixedJoinAction x h T (L p) ((0,L p)+I z)) := by
    ext z
    simpa only [I,ContinuousLinearMap.prod_apply,zero_apply,
      Prod.mk_add_mk,add_zero] using movingFixedJoinAction_eq hb h T p z
  rw [movingFixedJoinMiddle,he]
  have H' := second_fderiv_comp_affine I (0,L p) 0 (by simpa only [map_zero,add_zero] using H) v w
  simpa only [I,ContinuousLinearMap.prod_apply,zero_apply,map_zero,
    add_zero,fixedJoinMiddle_apply] using H'

lemma movingFixedJoinMiddle_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) (h T : ℝ)
    (p v w : TangentSpace 𝓘(ℝ,Model n) x)
    (H : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p)) :
    movingFixedJoinMiddle a h (T,(extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p))
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x v)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x w)=
        fixedJoinMiddle x h T p v w := by
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx' : x∈e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  have HL : ∀ v : TangentSpace 𝓘(ℝ,Model n) x, e.symmL ℝ x (e.continuousLinearMapAt ℝ x v)=v :=
    fun v => e.symmL_continuousLinearMapAt hx' v
  have HB : ContDiffAt ℝ 2
    (fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x)) h T
      (e.symmL ℝ ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
        (e.continuousLinearMapAt ℝ x p)))
    (0,e.symmL ℝ ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
      (e.continuousLinearMapAt ℝ x p)) := by
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,HL]
    exact H
  have HE := movingFixedJoinMiddle_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hx) h T
    (e.continuousLinearMapAt ℝ x p) (e.continuousLinearMapAt ℝ x v)
    (e.continuousLinearMapAt ℝ x w) HB
  dsimp only [e] at HL HE
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx] at HE
  simpa only [HL] using HE

end WeakMTWTransport

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MovingPrefix
import OAI.Analysis.BiholderTransport.Regularity.ActiveGraphLimit

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section JointMovingPrefix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,(ℝ×Model n)×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefix a q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp ((t,b),p)
    (contDiffAt_fst.snd.prodMk (contDiffAt_fst.fst.smul contDiffAt_snd)).contMDiffAt

lemma joint_movingPrefixChart_contDiffAt {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContDiffAt ℝ ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefixChart a c q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n))
    (by simpa only [extChartAt_source] using hc)).comp ((t,b),p)
      (joint_movingPrefix_contMDiffAt hb)).contDiffAt

lemma joint_movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (ht : t≠0)
    (hp : t • chartFiberInverse a b p∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefixEnergy a q.1.1 q.1.2 q.2) ((t,b),p) := by
  have hA : ContMDiffAt 𝓘(ℝ,(ℝ×Model n)×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (ℝ×Model n)×Model n=>movingNormal a (q.1.2,0)) ((t,b),p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp ((t,b),p)
      (contDiffAt_fst.snd.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,t • chartFiberInverse a b p⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb,chartFiberInverse] using hC
  exact ((hC'.comp ((t,b),p) (hA.prodMk (joint_movingPrefix_contMDiffAt hb))).contDiffAt.div
    contDiffAt_fst.fst ht)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingPrefix_at_center (a : M) (t : ℝ) (p : Model n) :
    movingPrefix a t (extChartAt 𝓘(ℝ,Model n) a a) p=riemannianExp a (t • p) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  rw [movingPrefix_eq hb]
  change riemannianExp _ (t • chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a) p)=_
  rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rfl

lemma movingPrefixEnergy_hessian_at_center {a : M} {p : Model n}
    (hp : p∈injectivityDomain a) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 (extChartAt 𝓘(ℝ,Model n) a a))) p d e=
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) e := by
  have hb := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hbase := (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  have hL (r : Model n) :
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a r=r := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
    exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
  have hp' : (1:ℝ) • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)) := by
    rw [hbase]
    simp only [hL]
    change (1:ℝ) • (show TangentSpace 𝓘(ℝ,Model n) a from p)∈injectivityDomain a
    rw [one_smul]
    exact hp
  have H := movingPrefixEnergy_hessian hb hp' d e
  rw [hbase] at H
  simpa only [hL,one_mul] using H

end JointMovingPrefix
end WeakMTWTransport

end
end

end OAI

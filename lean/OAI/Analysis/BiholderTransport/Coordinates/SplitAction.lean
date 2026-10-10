import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.RadialIdentity

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_injectivityDomain_near_one (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    ∀ᶠ t : ℝ in 𝓝 1,
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let Z : ℝ → TangentBundle 𝓘(ℝ,Model n) M := fun t => tangentScale (1-t) (sprayFlow t ⟨x,p⟩)
  have hZ : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_id).prodMk
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)))
  have hh : Z 1 ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
    change (1-(1:ℝ)) • (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈ injectivityDomain (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    rw [sub_self,zero_smul]
    exact zero_mem_injectivityDomain _
  exact hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hh)

lemma exists_minimizing_two_regular_legs {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) : ∃ t : ℝ, 0<t ∧ t<1 ∧
      t • p ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ t : ℝ in 𝓝[<] 1, 0<t ∧ t<1 ∧
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(shifted_injectivityDomain_near_one x p).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht0 ht1
    exact ⟨ht0,ht1,ht⟩
  obtain ⟨t,ht0,ht1,ht⟩ := H.exists
  exact ⟨t,ht0,ht1,contracted_minimizer_mem_injectivityDomain hp ht0 ht1,ht⟩

def splitNormalAction (x : M) (t : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x q.1) (riemannianExp x (t • q.2))/t +
    cost (riemannianExp x (t • q.2)) (riemannianExp x p)/(1-t)

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma normalCost_le_splitNormalAction (x : M) (p u v : TangentSpace 𝓘(ℝ,Model n) x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalCost x p u ≤ splitNormalAction x t p (u,v) := by
  have H := squared_dist_divided_action_le (riemannianExp x u)
    (riemannianExp x (t • v)) (riemannianExp x p) ht ht1
  convert H using 1 <;> simp only [normalCost,splitNormalAction,cost,div_div,mul_comm]

lemma splitNormalAction_contact {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    splitNormalAction x t p (0,p)=normalCost x p 0 := by
  have hseg : dist (riemannianExp x (t • p)) (riemannianExp x p)=(1-t)*‖p‖ := by
    rw [riemannianExp_smul,riemannianExp_eq_sprayFlow]
    exact sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      ht.le ht1.le (by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
  have H := minimizing_split_contact hp ht ht1
  unfold splitNormalAction normalCost
  rw [riemannianExp_zero]
  convert H using 1
  unfold cost
  rw [hseg]
  field_simp

lemma splitNormalAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fun z : TangentSpace 𝓘(ℝ,Model n) x ×
        (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) =>
      splitNormalAction x t z.1 z.2) (p,(0,p)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let a : V × (V×V) := (p,(0,p))
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x z.2.1) a :=
    (he _).comp a (contDiffAt_fst.comp a contDiffAt_snd).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x (t • z.2.2)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun z : V×(V×V) => t • z.2.2) a from by fun_prop).contMDiffAt
  have hw : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x z.1) a :=
    (he _).comp a contDiffAt_fst.contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (t • p),riemannianExp x p) := by
    dsimp only at hc₂
    rw [shifted_exp_endpoint] at hc₂
    simpa only [riemannianExp_smul] using hc₂
  exact ((hc₁'.comp a (hu.prodMk hv)).contDiffAt.div_const t).add
    ((hc₂'.comp a (hv.prodMk hw)).contDiffAt.div_const (1-t))

end WeakMTWTransport

end

end OAI

import Mathlib

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

def push (p : X) (f : E × E → G) (x : X × X) : G :=
  if x ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source then
    f (extChartAt I p x.1, extChartAt I p x.2) else 0

def liftSet (p : X) (K : Set (E × E)) : Set (X × X) :=
  (fun z : E × E => ((extChartAt I p).symm z.1,(extChartAt I p).symm z.2)) '' K

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

lemma liftSet_compact (p : X) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    IsCompact (liftSet p K) := by
  apply hc.image_of_continuousOn
  exact ((continuousOn_extChartAt_symm p).comp continuousOn_fst (fun z hz => (hK hz).1)).prodMk
    ((continuousOn_extChartAt_symm p).comp continuousOn_snd (fun z hz => (hK hz).2))

lemma support_push (p : X) (f : E × E → G) (K : Set (E × E))
    (hf : Function.support f ⊆ K) : Function.support (push p f) ⊆ liftSet p K := by
  intro x hx
  have hs : x ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
    by_contra hh
    exact hx (by simp only [push,ite_eq_right hh])
  refine ⟨(extChartAt I p x.1,extChartAt I p x.2), hf ?_,?_⟩
  · simpa only [Function.mem_support,push,ite_eq_left hs] using hx
  · simp only [(extChartAt I p).left_inv hs.1,(extChartAt I p).left_inv hs.2]

lemma push_apply (p : X) (f : E × E → G) {z : E × E}
    (hz : z ∈ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    push p f ((extChartAt I p).symm z.1,(extChartAt I p).symm z.2) = f z := by
  simp only [push,Set.mem_prod,(extChartAt I p).map_target hz.1,(extChartAt I p).map_target hz.2,
    and_self,ite_true,(extChartAt I p).right_inv hz.1,(extChartAt I p).right_inv hz.2]

variable [T2Space X]

lemma tsupport_push (p : X) (f : E × E → G) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target)
    (hf : Function.support f ⊆ K) : tsupport (push p f) ⊆ liftSet p K :=
  closure_minimal (support_push p f K hf) (liftSet_compact p K hc hK).isClosed

lemma push_joint_continuousAt {P : Type*} [TopologicalSpace P]
    (p : X) (f : P → E × E → G) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target)
    (hf : ∀ t, Function.support (f t) ⊆ K) (t : P)
    (hcont : ∀ z, ContinuousAt (fun v : P × (E × E) => f v.1 v.2) (t,z)) (x : X × X) :
    ContinuousAt (fun v : P × (X × X) => push p (f v.1) v.2) (t,x) := by
  by_cases hx : x ∈ liftSet p K
  · have hsrc := liftSet_source p K hK hx
    have hco : ContinuousAt (fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2)) x :=
      ((continuousAt_extChartAt' hsrc.1).comp continuousAt_fst).prodMk
        ((continuousAt_extChartAt' hsrc.2).comp continuousAt_snd)
    have he : (fun v : P × (X × X) => push p (f v.1) v.2) =ᶠ[𝓝 (t,x)]
        fun v => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2) := by
      have hn : {v : P × (X × X) | v.2 ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source} ∈ 𝓝 (t,x) :=
        (show ContinuousAt (Prod.snd : P × (X × X) → X × X) (t,x) from continuousAt_snd).preimage_mem_nhds
          (((show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p).prod
            (show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p)).mem_nhds hsrc)
      filter_upwards [hn] with v hv
      simp only [push,ite_eq_left hv]
    have hprod : ContinuousAt (fun v : P × (X × X) =>
        (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2))) (t,x) := by
      exact continuousAt_fst.prodMk (ContinuousAt.comp
        (g := fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2))
        (f := Prod.snd) hco continuousAt_snd)
    have hc' : ContinuousAt (fun v : P × (X × X) => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2)) (t,x) := by
      exact ContinuousAt.comp (g := fun v : P × (E × E) => f v.1 v.2)
        (f := fun v : P × (X × X) => (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2)))
        (hcont (extChartAt I p x.1,extChartAt I p x.2)) hprod
    exact hc'.congr_of_eventuallyEq he
  · apply continuousAt_const.congr_of_eventuallyEq
    have hn := (continuous_snd : Continuous (Prod.snd : P × (X × X) → X × X)).continuousAt (x := (t,x)) |>.preimage_mem_nhds
      ((liftSet_compact p K hc hK).isClosed.isOpen_compl.mem_nhds hx)
    filter_upwards [hn] with v hv
    exact Function.notMem_support.mp (fun h => hv (support_push p (f v.1) K (hf v.1) h))

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI

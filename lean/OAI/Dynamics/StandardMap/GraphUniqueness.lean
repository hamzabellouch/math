import OAI.Dynamics.StandardMap.GraphSubsetCalculus

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma graph_local_coincidence (F : ℝ × ℝ → ℝ) (b c : ℝ → ℝ)
    (s : Set ℝ) (x u v : ℝ)
    (hD : HasStrictFDerivAt F
      (u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (hv : v ≠ 0) (he : b x=c x) (hb : ContinuousWithinAt b s x)
    (hc : ContinuousWithinAt c s x)
    (hFb : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x))
    (hFc : ∀ᶠ y in 𝓝[s] x, F (y,c y)=F (x,b x)) :
    b =ᶠ[𝓝[s] x] c := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := v⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,hv]
    · apply ContinuousLinearMap.ext; intro z; simp [L,hv]
  have hbpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
  have hcpair : Tendsto (fun y => (y,c y)) (𝓝[s] x) (𝓝 (x,b x)) := by
    rw [he]
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hc
  filter_upwards [hbpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),
    hcpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hFb,hFc] with y hyb hyc h1 h2
  exact (hyb.mp h1).symm.trans (hyc.mp h2)

lemma eqOn_of_locally_coincident {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] (s : Set α) (f g : α → β)
    (hs : IsPreconnected s) (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hloc : ∀ x ∈ s, f x=g x → f =ᶠ[𝓝[s] x] g)
    (x : α) (hx : x ∈ s) (he : f x=g x) : EqOn f g s := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hc : IsClosed {y : s | f y=g y} := isClosed_eq hf.domRestrict hg.domRestrict
  have ho : IsOpen {y : s | f y=g y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hh := hloc y y.property hy
    have ht : Tendsto (Subtype.val : s → α) (𝓝 y) (𝓝[s] (y:α)) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.tendsto y,Filter.Eventually.of_forall (fun z => z.property)⟩
    exact ht.eventually hh
  have hu : {y : s | f y=g y}=univ := IsClopen.eq_univ (s := {y : s | f y=g y}) ⟨hc,ho⟩ ⟨⟨x,hx⟩,he⟩
  intro y hy
  have hh : (⟨y,hy⟩ : s) ∈ ({z : s | f z=g z}) := by rw [hu]; trivial
  exact hh

lemma regular_graphs_coincide (F : ℝ × ℝ → ℝ) (b c : ℝ → ℝ)
    (s : Set ℝ) (hs : IsPreconnected s) (hb : ContinuousOn b s) (hc : ContinuousOn c s)
    (L : ℝ) (hFb : ∀ y ∈ s, F (y,b y)=L) (hFc : ∀ y ∈ s, F (y,c y)=L)
    (hreg : ∀ y ∈ s, ∃ u v : ℝ, v ≠ 0 ∧ HasStrictFDerivAt F
      (u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ) (y,b y))
    (x : ℝ) (hx : x ∈ s) (he : b x=c x) : EqOn b c s := by
  apply eqOn_of_locally_coincident s b c hs hb hc _ x hx he
  intro y hy hey
  obtain ⟨u,v,hv,hD⟩:=hreg y hy
  apply graph_local_coincidence F b c s y u v hD hv hey (hb y hy) (hc y hy)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFb z hz,hFb y hy]
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFc z hz,hFb y hy]
end StandardMapEntropy

end OAI

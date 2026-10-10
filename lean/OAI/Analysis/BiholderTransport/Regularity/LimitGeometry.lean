import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.FirstCutConvex
import OAI.Analysis.BiholderTransport.Geodesics.GraphGlobalMinimal

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff Pointwise

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma continuous_graphProjection_family (u : M → ℝ) :
    Continuous (fun q : ℝ × subgradientGraph (n := n) u => graphProjection u q.1 q.2) :=
  contMDiff_riemannianExp.continuous.comp
    (contMDiff_tangentScale.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

lemma graph_global_min_at_left_limit {u : M → ℝ} (hu : Continuous u)
    {T : ℝ} (hT : 0<T)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u) :
    T • z.1.2 ∈ minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u T z)/T ≤
        u a+cost a (graphProjection u T z)/T := by
  have H : ∀ᶠ t in 𝓝[<] T, t • z.1.2 ∈ minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t ≤
        u a+cost a (graphProjection u t z)/t := by
    filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htT
    exact global_min_of_injective_graphProjection hu ht (hinj t ⟨ht,htT⟩) z
  refine ⟨?_,?_⟩
  · have hcs : Continuous (fun t : ℝ => t • z.1.2) := continuous_id.smul continuous_const
    apply (isClosed_minimizingVectors z.1.1).mem_of_tendsto
      (hcs.continuousAt.tendsto.mono_left (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
    exact H.mono (fun _ h => h.1)
  · intro a
    have hc (b : M) : ContinuousAt (fun t => u b+cost b (graphProjection u t z)/t) T :=
      continuousAt_const.add (((continuous_cost_right b).continuousAt.comp
        ((continuous_graphProjection_family u).continuousAt.comp
          (f := fun t : ℝ => (t,z)) (continuousAt_id.prodMk continuousAt_const))).div continuousAt_id hT.ne')
    exact le_of_tendsto_of_tendsto (b := 𝓝[<] T)
      ((hc z.1.1).tendsto.mono_left nhdsWithin_le_nhds)
      ((hc a).tendsto.mono_left nhdsWithin_le_nhds) (H.mono (fun _ h => h.2 a))

lemma WeakMTW.active_hull_nonconjugate_of_minimizing
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} {x : M}
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hmin : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    Function.Injective (fderiv ℝ (fun q => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (T • p)) (riemannianExp x q)) (T • p)) := by
  apply hmtw.convexHull_nonconjugate (S := T • activeLogs (n := n) v x)
  · rw [convexHull_smul]
    rintro _ ⟨q,hq,rfl⟩
    exact hmin q hq
  · rintro _ ⟨q,hq,rfl⟩
    exact riemannianExp_interior_nonconjugate
      (contracted_minimizer_mem_injectivityDomain hq.1 hT hT1)
  · rw [convexHull_smul]
    exact ⟨p,hp,rfl⟩

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_hull_interior_below_minimizing {v : M → ℝ} {x : M}
    {T : ℝ} (hT : 0<T)
    (hmin : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x) :
    ∀ t ∈ Ioo (0:ℝ) T, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • p ∈ injectivityDomain x := by
  intro t ht p hp
  have H := contracted_minimizer_mem_injectivityDomain (hmin p hp)
    (div_pos ht.1 hT) ((div_lt_one hT).mpr ht.2)
  simpa only [smul_smul,div_mul_cancel₀ _ hT.ne'] using H

end

open Set Filter
open scoped Topology

lemma isPreconnected_fiber_of_mem_closure_bijective
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (F : P → X → Y) (hF : Continuous (fun q : P × X => F q.1 q.2))
    {a : P} (ha : a ∈ closure {p | Function.Bijective (F p)}) (y : Y) :
    IsPreconnected {x | F a x = y} := by
  have hFa : Continuous (F a) := hF.comp (continuous_const.prodMk continuous_id)
  have hs : IsClosed {x | F a x = y} := isClosed_eq hFa continuous_const
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hs).mpr
  intro A B hA hB hcover hAB
  by_contra hnot
  push Not at hnot
  obtain ⟨x,hx,hxA⟩ := Set.not_subset.mp hnot.1
  obtain ⟨z,hz,hzB⟩ := Set.not_subset.mp hnot.2
  have hxB : x ∈ B := (hcover hx).resolve_left hxA
  have hzA : z ∈ A := (hcover hz).resolve_right hzB
  obtain ⟨U,V,hU,hV,hAU,hBV,hUV⟩ := normal_separation hA hB hAB
  let K := (U ∪ V)ᶜ
  have hK : IsCompact K := (hU.union hV).isClosed_compl.isCompact
  have H : ∀ᶠ q : P × Y in 𝓝 (a,y), ∀ b ∈ K, F q.1 b ≠ q.2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro b hb
    have hbne : F a b ≠ y := by
      intro he
      exact hb ((hcover he).imp (fun h => hAU h) (fun h => hBV h))
    have hf : Continuous (fun q : (P × Y) × X => F q.1.1 q.2) :=
      hF.comp ((continuous_fst.fst).prodMk continuous_snd)
    exact (isOpen_ne_fun hf continuous_fst.snd).mem_nhds hbne
  obtain ⟨O,hO,W,hW,hOW⟩ := mem_nhds_prod_iff.mp H
  obtain ⟨N,hNW,hN,hyN,hNc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp (inferInstance : LocallyConnectedSpace Y)) y W hW
  have Hx : ∀ᶠ p in 𝓝 a, F p x ∈ N := by
    have hc : ContinuousAt (fun p => F p x) a :=
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hc.preimage_mem_nhds (hx.symm ▸ hN.mem_nhds hyN)
  have Hz : ∀ᶠ p in 𝓝 a, F p z ∈ N := by
    have hc : ContinuousAt (fun p => F p z) a :=
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hc.preimage_mem_nhds (hz.symm ▸ hN.mem_nhds hyN)
  have HO : ∀ᶠ p in 𝓝 a, p ∈ O := hO
  obtain ⟨p,hp,hpO,hpx,hpz⟩ :=
    ((mem_closure_iff_frequently.mp ha).and_eventually (HO.and (Hx.and Hz))).exists
  have hpC : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
  have hpconn : IsPreconnected (F p ⁻¹' N) :=
    hNc.isPreconnected.preimage_of_isClosedMap hp.1 hpC.isClosedMap
      (fun w _ => hp.2 w)
  have hsub : F p ⁻¹' N ⊆ U ∪ V := by
    intro b hb
    by_contra hn
    exact hOW (show (p,F p b) ∈ O ×ˢ W from ⟨hpO,hNW hb⟩) b hn rfl
  obtain ⟨b,hb,hbU,hbV⟩ := hpconn U V hU hV hsub
    ⟨z,hpz,hAU hzA⟩ ⟨x,hpx,hBV hxB⟩
  exact Set.disjoint_left.mp hUV hbU hbV

lemma fiber_subsingleton_of_preconnected_isolated
    {X : Type*} [TopologicalSpace X] [T1Space X] {s : Set X}
    (hs : IsPreconnected s)
    (hisol : ∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ s ⊆ {x}) :
    s.Subsingleton := by
  intro x hx y hy
  obtain ⟨U,hU,hxU,hUs⟩ := hisol x hx
  by_contra hxy
  have hcov : s ⊆ U ∪ ({x} : Set X)ᶜ := by
    intro z hz
    by_cases he : z=x
    · exact Or.inl (he.symm ▸ hxU)
    · exact Or.inr he
  obtain ⟨z,hzs,hzU,hzne⟩ := hs U ({x} : Set X)ᶜ hU isClosed_singleton.isOpen_compl hcov
    ⟨x,hx,hxU⟩ ⟨y,hy,Ne.symm hxy⟩
  exact hzne (hUs ⟨hzU,hzs⟩)

end WeakMTWTransport

end

end OAI

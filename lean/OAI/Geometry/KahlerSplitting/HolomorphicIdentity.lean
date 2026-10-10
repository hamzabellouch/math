import OAI.Geometry.KahlerSplitting.ProductCharts

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
section ComplexIdentity
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_eqOn_of_convex_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : Convex ℝ U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  intro y hy
  let l : ℂ →ᴬ[ℂ] E := ContinuousAffineMap.lineMap x y
  let L : ℂ →L[ℝ] E := ((ContinuousLinearMap.id ℂ ℂ).smulRight (y - x)).restrictScalars ℝ
  have he : ∀ z : ℂ, l z = L z + x := fun z ↦ rfl
  have hl0 : l 0 = x := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hl1 : l 1 = y := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hopen : IsOpen (l ⁻¹' U) := hU.preimage l.continuous
  have hconv : Convex ℝ (l ⁻¹' U) := by
    change Convex ℝ ((fun z ↦ L z + x) ⁻¹' U)
    exact (hc.translate_preimage_left x).linear_preimage L.toLinearMap
  have hf' : DifferentiableOn ℂ (f ∘ l) (l ⁻¹' U) :=
    hf.comp l.differentiableOn (mapsTo_preimage _ _)
  have hg' : DifferentiableOn ℂ (g ∘ l) (l ⁻¹' U) :=
    hg.comp l.differentiableOn (mapsTo_preimage _ _)
  have hlocal : (f ∘ l) =ᶠ[𝓝 0] (g ∘ l) :=
    hfg.comp_tendsto (hl0 ▸ l.continuous.continuousAt)
  have hzero : (0 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl0] using hx
  have hone : (1 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl1] using hy
  have h := (hf'.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hg'.analyticOnNhd hopen) hconv.isPreconnected hzero hlocal hone
  simpa only [Function.comp_apply, hl1] using h

theorem holomorphic_eqOn_of_preconnected_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : E | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz.2
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff.mp hz.1 (Metric.ball z r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have heq : EqOn f g (Metric.ball z r) :=
      holomorphic_eqOn_of_convex_of_eventuallyEq Metric.isOpen_ball (convex_ball z r)
        (hf.mono hrU) (hg.mono hrU) hwB hwV
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr) heq
  intro z hz
  exact (hVU hz).eq_of_nhds

end ComplexIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldIdentity
open Filter Topology
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n : ℕ} {X : ComplexManifold n}

theorem holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f g : E → X.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, E) (model n) f U)
    (hg : MDifferentiableOn 𝓘(ℂ, E) (model n) g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : E | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have hcg : ContinuousAt g z := (hg.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have : (𝓝[V] z).NeBot := mem_closure_iff_clusterPt.mp hz.1
    have heq : f z = g z := tendsto_nhds_unique_of_eventuallyEq
      hcf.continuousWithinAt hcg.continuousWithinAt
      (Filter.mem_of_superset self_mem_nhdsWithin fun w (hw : w ∈ V) ↦ hw.eq_of_nhds)
    let c := extChartAt (model n) (f z)
    have hsrc : c.source ∈ 𝓝 (f z) := extChartAt_source_mem_nhds (I := model n) (f z)
    have hN : U ∩ (f ⁻¹' c.source ∩ g ⁻¹' c.source) ∈ 𝓝 z :=
      inter_mem (hU.mem_nhds hz.2) (inter_mem (hcf hsrc) (hcg (heq ▸ hsrc)))
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : DifferentiableOn ℂ (c ∘ f) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ f) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.1)).comp a
          (hf.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    have hgc : DifferentiableOn ℂ (c ∘ g) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ g) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.2)).comp a
          (hg.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff.mp hz.1 (Metric.ball z r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hchart : EqOn (c ∘ f) (c ∘ g) (Metric.ball z r) :=
      holomorphic_eqOn_of_convex_of_eventuallyEq Metric.isOpen_ball (convex_ball z r)
        hfc hgc hwB (hwV.mono fun a ha ↦ congrArg c ha)
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr) fun a ha ↦
      c.injOn (hrN ha).2.1 (hrN ha).2.2 (hchart ha)
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldSourceIdentity
open Filter Topology
open scoped Manifold
variable {m n : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}

theorem holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq
    {U : Set M.Carrier} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : M.Carrier → X.Carrier}
    (hf : MDifferentiableOn (model m) (model n) f U)
    (hg : MDifferentiableOn (model m) (model n) g U)
    {x : M.Carrier} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : M.Carrier | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    let e := chartAt (Model m) z
    have hzs : z ∈ e.source := mem_chart_source _ _
    have hzt : e z ∈ e.target := e.map_source hzs
    have hcz : ContinuousAt e z := e.continuousAt hzs
    have hcs : ContinuousAt e.symm (e z) := e.symm.continuousAt hzt
    have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e z) := by
      refine inter_mem (e.open_target.mem_nhds hzt) (hcs ?_)
      simpa only [e.left_inv hzs] using hU.mem_nhds hz.2
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (f ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hf.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hgc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (g ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hg.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hB : e.source ∩ e ⁻¹' Metric.ball (e z) r ∈ 𝓝 z :=
      inter_mem (e.open_source.mem_nhds hzs) (hcz (Metric.ball_mem_nhds _ hr))
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff_nhds.mp hz.1 _ hB
    have hwgerm : (f ∘ e.symm) =ᶠ[𝓝 (e w)] (g ∘ e.symm) := by
      apply hwV.comp_tendsto
      have h := e.symm.continuousAt (e.map_source hwB.1)
      change Tendsto e.symm (𝓝 (e w)) (𝓝 (e.symm (e w))) at h
      simpa only [e.left_inv hwB.1] using h
    have heq := holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      Metric.isOpen_ball (convex_ball (e z) r).isPreconnected hfc hgc hwB.2 hwgerm
    exact Filter.mem_of_superset hB fun a ha ↦ by
      change f a = g a
      simpa only [Function.comp_apply, e.left_inv ha.1] using heq ha.2
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldSourceIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section LocalProductSeparation
variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem independent_second_of_fderiv_zero
    {U : Set E₁} {V : Set E₂} (hU : IsOpen U) (hV : IsOpen V)
    (hVc : IsPreconnected V) {f : E₁ × E₂ → F}
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hzero : ∀ p ∈ U ×ˢ V, ∀ v : E₂, fderiv ℂ f p (0, v) = 0)
    {a : E₁} (ha : a ∈ U) {b c : E₂} (hb : b ∈ V) (hc : c ∈ V) :
    f (a, b) = f (a, c) := by
  have hd (y : E₂) (hy : y ∈ V) :
      HasFDerivAt (fun t : E₂ ↦ f (a, t)) (0 : E₂ →L[ℂ] F) y := by
    have hp : HasFDerivAt (fun t : E₂ ↦ (a, t))
        (ContinuousLinearMap.inr ℂ E₁ E₂) y := by
      have hh := (hasFDerivAt_const (𝕜 := ℂ) a y).prodMk (hasFDerivAt_id (𝕜 := ℂ) y)
      have he : (ContinuousLinearMap.prod (0 : E₂ →L[ℂ] E₁)
          (ContinuousLinearMap.id ℂ E₂)) = ContinuousLinearMap.inr ℂ E₁ E₂ := by
        ext v <;> rfl
      rw [he] at hh
      exact hh
    have hh := ((hf (a, y) ⟨ha, hy⟩).differentiableAt
      ((hU.prod hV).mem_nhds ⟨ha, hy⟩)).hasFDerivAt.comp y hp
    have he : fderiv ℂ f (a, y) ∘L ContinuousLinearMap.inr ℂ E₁ E₂ = 0 := by
      ext v
      exact hzero (a, y) ⟨ha, hy⟩ v
    rw [he] at hh
    exact hh
  exact hV.is_const_of_fderiv_eq_zero hVc
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd y hy).fderiv) hb hc

end LocalProductSeparation
end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem finite_curveArea_removable_at [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball p R \ {p}))
    (ha : curveArea g f (ball p R \ {p}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f p x) (ball p R) := by
  have him : (fun z : ℂ ↦ p + (1:ℝ) • z) '' (ball 0 R \ {0}) = ball p R \ {p} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa [dist_eq_norm, add_sub_cancel_left, add_eq_left] using hw
    · intro hz
      refine ⟨z-p,?_,by simp⟩
      simpa [dist_eq_norm, sub_eq_zero] using hz
  have hmap : MapsTo (fun z : ℂ ↦ p+z) (ball 0 R \ {0}) (ball p R \ {p}) := by
    intro z hz
    rw [← him]
    exact ⟨z,hz,by simp⟩
  have hq : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (p+z)) (ball 0 R \ {0}) :=
    hf.comp (((differentiable_const p).add differentiable_id).mdifferentiable.mdifferentiableOn) hmap
  have haq : curveArea g (fun z ↦ f (p+z)) (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞) := by
    have he := curveArea_positive_affine g (ball 0 R \ {0})
      (isOpen_ball.sdiff isClosed_singleton).measurableSet p (by norm_num : (0:ℝ)<1)
      (fun z hz ↦ hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (him ▸ hz)))
    rw [him] at he
    simpa only [one_smul] using he.trans_ne ha
  obtain ⟨x,hx⟩ := finite_curveArea_removable g hR hq haq
  have hback : MapsTo (fun z : ℂ ↦ z-p) (ball p R) (ball 0 R) := by
    intro z hz; simpa only [mem_ball,dist_eq_norm,sub_zero] using hz
  have heq : (Function.update (fun z ↦ f (p+z)) 0 x) ∘ (fun z : ℂ ↦ z-p) =
      Function.update f p x := by
    funext z
    by_cases hz : z = p
    · subst z; simp
    · simp only [Function.comp_apply,Function.update_of_ne hz,
        Function.update_of_ne (sub_ne_zero.mpr hz),add_sub_cancel]
  refine ⟨x,?_⟩
  rw [← heq]
  exact hx.comp ((differentiable_id.sub_const p).mdifferentiable.mdifferentiableOn) hback

theorem finite_curveArea_remove_finite [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hA : A.Finite)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (Ω \ A))
    (ha : curveArea g f (Ω \ A) ≠ (⊤ : ℝ≥0∞)) :
    ∃ F : ℂ → X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F Ω ∧ EqOn F f (Ω \ A) := by
  classical
  have hloc : ∀ p ∈ Ω ∩ A, ∃ x : X.Carrier,
      MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (Function.update f p x) p := by
    intro p hp
    have hN : Ω \ (A \ {p}) ∈ 𝓝 p :=
      (hΩ.sdiff (hA.sdiff : (A \ {p}).Finite).isClosed).mem_nhds ⟨hp.1,by simp⟩
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp hN
    have hsub' : ball p R \ {p} ⊆ Ω \ A := by
      intro z hz
      have hh := hsub hz.1
      refine ⟨hh.1,fun hzA ↦ hh.2 ⟨hzA,hz.2⟩⟩
    obtain ⟨x,hx⟩ := finite_curveArea_removable_at g hR (hf.mono hsub')
      (ne_top_of_le_ne_top ha (curveArea_mono g f hsub'))
    exact ⟨x,hx.mdifferentiableAt (ball_mem_nhds p hR)⟩
  choose x hx using hloc
  let F : ℂ → X.Carrier := fun p ↦ if hp : p ∈ Ω ∩ A then x p hp else f p
  have heq : EqOn F f (Ω \ A) := by
    intro p hp
    exact dite_eq_right (fun hh ↦ hp.2 hh.2)
  refine ⟨F,?_,heq⟩
  intro p hp
  by_cases hpA : p ∈ A
  · have hd := hx p ⟨hp,hpA⟩
    apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [(hA.sdiff : (A \ {p}).Finite).isClosed.isOpen_compl.mem_nhds
      (show p ∉ A \ {p} by simp)] with z hz
    by_cases hzp : z = p
    · subst z; simp [F, hp,hpA]
    · have hzA : z ∉ A := fun hh ↦ hz ⟨hh,hzp⟩
      simp [F,hzA,Function.update_of_ne hzp]
  · have hd := hf.mdifferentiableAt ((hΩ.sdiff hA.isClosed).mem_nhds ⟨hp,hpA⟩)
    apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hpA] with z hz
    change z ∉ A at hz
    simp [F,hz]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem bounded_curveArea_subsequence_with_removed_limit [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKn : K.Nonempty) (hKΩ : K ⊆ Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (C : ℝ≥0) (hC : ∀ j, curveArea g (f j) K ≤ (C : ℝ≥0∞)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∃ F : ℂ → X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F (interior K) ∧
        TendstoLocallyUniformlyOn (f ∘ σ) F atTop (interior K \ A) := by
  obtain ⟨σ,hσ,A,hA,hAK,F,hF,hconv⟩ :=
    bounded_curveArea_holomorphic_subsequence g f hΩ hK hKn hKΩ hf C hC
  have hU : IsOpen (interior K \ A) := isOpen_interior.sdiff hA.isClosed
  have hUK : interior K \ A ⊆ K := sdiff_subset.trans interior_subset
  have ha : curveArea g F (interior K \ A) ≤ (C : ℝ≥0∞) :=
    locally_uniform_curveArea_le g hU
      (fun j ↦ (hf (σ j)).mono (hUK.trans hKΩ)) hconv
      (fun j ↦ (curveArea_mono g (f (σ j)) hUK).trans (hC (σ j)))
  obtain ⟨G,hG,hGF⟩ := finite_curveArea_remove_finite g isOpen_interior hA hF
    (ne_top_of_le_ne_top ENNReal.coe_ne_top ha)
  exact ⟨σ,hσ,A,hA,hAK,G,hG,hconv.congr_right hGF.symm⟩

end UniversalCoverSplitting

end

end OAI

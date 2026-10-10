import Mathlib
import OAI.Analysis.SymmetricDomains.ClosedMaximizerRelation
import OAI.Analysis.SymmetricDomains.LocalMaxGraphParameter
import OAI.Analysis.SymmetricDomains.CayleyTangentBound

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set MeasureTheory Module Filter
open scoped Topology ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def offsetGraphConormal (L : E →ₗ[ℝ] F) (r : F →L[ℝ] ℝ) :
    (F →L[ℝ] ℝ) →ᵃ[ℝ] L.graph.dualAnnihilator where
  toFun b := graphConormal L (b+r)
  linear := graphConormal L
  map_vadd' p v := by
    change graphConormal L ((v+p)+r) = graphConormal L v+graphConormal L (p+r)
    rw [add_assoc,map_add]

theorem offsetGraphConormal_surjective [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (r : F →L[ℝ] ℝ) : Function.Surjective (offsetGraphConormal L r) := by
  intro q
  obtain ⟨b,hb⟩ := graphConormal_surjective L q
  refine ⟨b-r,?_⟩
  simpa only [offsetGraphConormal,AffineMap.coe_mk,sub_add_cancel] using hb

theorem supported_graph_conormals
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (F →L[ℝ] ℝ)] [BorelSpace (F →L[ℝ] ℝ)]
    (μ : Measure E) (ν : Measure (F →L[ℝ] ℝ))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) (φ : ℕ → E → ℝ) (g : ℕ → E → F)
    (S : ℕ → Set (E × (F →L[ℝ] ℝ))) (hS : ∀ i, MeasurableSet (S i))
    (hφ : ∀ i q, q ∈ S i → AnalyticAt ℝ (φ i) q.1)
    (hg : ∀ i q, q ∈ S i → AnalyticAt ℝ (g i) q.1)
    (bad : ℕ → Set E) (hbad : ∀ i, μ (bad i) = 0)
    (T : Set (E × (F →L[ℝ] ℝ))) (hT : (μ.prod ν) T ≠ 0)
    (hcover : T ⊆ ⋃ i, selfDualGraphParameter e (φ i) (g i) '' S i)
    (r : ℕ → E → F →L[ℝ] ℝ) :
    ∃ i p, p ∉ bad i ∧ ∃ b : Fin (finrank ℝ
        (fderiv ℝ (g i) p).toLinearMap.graph.dualAnnihilator) → (F →L[ℝ] ℝ),
      (∀ j, (p,b j) ∈ S i) ∧
      LinearIndependent ℝ (fun j => offsetGraphConormal
        (fderiv ℝ (g i) p).toLinearMap (r i p) (b j)) := by
  have hd : ∀ i, DifferentiableOn ℝ (selfDualGraphParameter e (φ i) (g i)) (S i) := by
    intro i q hq
    exact (differentiableAt_selfDualGraphParameter e (hφ i q hq) (hg i q hq) q.2).differentiableWithinAt
  obtain ⟨i,p,hp,hfiber⟩ := supported_positive_fiber μ ν S hS
    (fun i => selfDualGraphParameter e (φ i) (g i)) hd bad hbad T hT hcover
  obtain ⟨b,hb,hi⟩ := exists_independent_affine_images_of_positive_measure ν hfiber
    (offsetGraphConormal (fderiv ℝ (g i) p).toLinearMap (r i p))
    (offsetGraphConormal_surjective _ _)
  exact ⟨i,p,hp,b,hb,hi⟩

end

open Set Filter MeasureTheory
open scoped Topology

theorem analytic_real_zero_null {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℝ} (hU : MeasurableSet U) (hc : IsPreconnected U)
    {f : ℝ → F} (hf : AnalyticOnNhd ℝ f U) {p : ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    volume {x | x ∈ U ∧ f x = 0} = 0 := by
  have ha := hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc
  rcases ha with ha | ha
  · exact (hne (ha hp)).elim
  · have hb := ae_restrict_le_codiscreteWithin (μ := volume) hU ha
    have hd := (ae_restrict_iff' hU).mp hb
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hd] with x hx
    exact fun h => hx h.1 h.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialPlane (p : E × ℝ) (q : E × ℝ) : E × ℝ := p + (q.2 • q.1, q.2)

def radialLine (p : E × ℝ) (y : E) : ℝ →ᵃ[ℝ] E × ℝ where
  toFun t := radialPlane p (y,t)
  linear := (LinearMap.id.smulRight y).prod LinearMap.id
  map_vadd' t u := by
    change p + ((u+t) • y,u+t) = (u • y,u)+(p+(t • y,t))
    simp only [add_smul]
    change p + ((u • y,u)+(t • y,t)) = (u • y,u)+(p+(t • y,t))
    abel

theorem radialPlane_analytic (p : E × ℝ) (q : E × ℝ) : AnalyticAt ℝ (radialPlane p) q := by
  exact analyticAt_const.add ((analyticAt_snd.smul analyticAt_fst).prod analyticAt_snd)

theorem radialLine_analytic (p : E × ℝ) (y : E) (t : ℝ) : AnalyticAt ℝ (radialLine p y) t := by
  exact (radialPlane_analytic p (y,t)).comp (analyticAt_const.prod analyticAt_id)

theorem analytic_zero_null_convex [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  let Z : Set (E × ℝ) := {x | x ∈ U ∧ f x = 0}
  have hZ : MeasurableSet Z := by
    have hm : Measurable (U.piecewise f (fun _ => 0)) :=
      hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
    convert hU.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
    ext x
    by_cases hx : x ∈ U <;> simp [Z,hx]
  have hr : Continuous (radialPlane p) := continuous_iff_continuousAt.mpr fun q => (radialPlane_analytic p q).continuousAt
  have hn : (μ.prod volume) (radialPlane p ⁻¹' Z) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hZ.preimage hr.measurable)
    apply Eventually.of_forall
    intro y
    let I : Set ℝ := radialLine p y ⁻¹' U
    have hI : IsOpen I := hU.preimage (continuous_iff_continuousAt.mpr fun t => (radialLine_analytic p y t).continuousAt)
    have hr0 : radialLine p y 0 = p := by
      change p + ((0 : ℝ) • y,(0 : ℝ)) = p
      rw [zero_smul]
      exact add_zero p
    have h0 : (0 : ℝ) ∈ I := by change radialLine p y 0 ∈ U; simpa only [hr0] using hp
    have hf0 : f (radialLine p y 0) ≠ 0 := by simpa only [hr0] using hne
    exact analytic_real_zero_null hI.measurableSet (hc.affine_preimage (radialLine p y)).isPreconnected
      (fun t ht => (hf _ ht).comp (radialLine_analytic p y t)) h0 hf0
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ.prod volume) (s := radialPlane p ⁻¹' Z)
    (fun q _ => (radialPlane_analytic p q).differentiableAt.differentiableWithinAt) hn
  have hplane : (μ.prod volume) (Set.univ ×ˢ {p.2}) = 0 := by
    rw [Measure.prod_prod,measure_singleton,mul_zero]
  apply measure_mono_null (t := radialPlane p '' (radialPlane p ⁻¹' Z) ∪ (Set.univ ×ˢ {p.2}))
      _ (measure_union_null himg hplane)
  intro x hx
  by_cases ht : x.2 = p.2
  · exact Or.inr ⟨mem_univ _,ht⟩
  · left
    let q : E × ℝ := ((x.2-p.2)⁻¹ • (x.1-p.1),x.2-p.2)
    have hq : radialPlane p q = x := by
      ext
      · simp only [radialPlane,q,Prod.fst_add,smul_smul]
        rw [mul_inv_cancel₀ (sub_ne_zero.mpr ht),one_smul]
        abel
      · simp [radialPlane,q]
    exact ⟨q,by simpa only [mem_preimage,hq] using hx,hq⟩

theorem analytic_zero_null_connected [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  have hball : ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U := fun x hx =>
    Metric.isOpen_iff.mp hU x hx
  choose! r hr hsub using hball
  obtain ⟨T,hTU,hTc,hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := U) (f := fun x => Metric.ball x (r x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x hx)))
  have hn : ∀ x ∈ T, (μ.prod volume) {y | y ∈ Metric.ball x (r x) ∧ f y = 0} = 0 := by
    intro x hx
    have hxu := hTU hx
    have he : ∃ y ∈ Metric.ball x (r x), f y ≠ 0 := by
      by_contra! he
      have hz : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [Metric.ball_mem_nhds x (hr x hxu)] with y hy
        exact he y hy
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hxu hz hp)
    obtain ⟨y,hy,hfy⟩ := he
    exact analytic_zero_null_convex μ Metric.isOpen_ball (convex_ball x (r x))
      (hf.mono (hsub x hxu)) hy hfy
  apply measure_mono_null (t := ⋃ x ∈ T, {y | y ∈ Metric.ball x (r x) ∧ f y = 0})
    _ ((measure_biUnion_null_iff hTc).mpr hn)
  intro y hy
  obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hcov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy.2⟩

theorem analytic_zero_null [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E} (hp : p ∈ U) (hne : f p ≠ 0) : μ {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  rcases subsingleton_or_nontrivial E with hs | hnt
  · have hz : {x | x ∈ U ∧ f x = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ((congrArg f (Subsingleton.elim p x)).trans hx.2)
    rw [hz,measure_empty]
  · obtain ⟨n,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
    let e : E ≃L[ℝ] ((Fin n → ℝ) × ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by simpa [Module.finrank_prod,Module.finrank_pi_fintype,Nat.succ_eq_add_one] using hd)
    let U' := e.symm ⁻¹' U
    let f' := f ∘ e.symm
    have hf' : AnalyticOnNhd ℝ f' U' := fun x hx => (hf _ hx).comp (e.symm.analyticAt x)
    have hp' : e p ∈ U' := by simpa only [U',mem_preimage,e.symm_apply_apply] using hp
    have he : f' (e p) ≠ 0 := by simpa only [f',Function.comp_apply,e.symm_apply_apply] using hne
    have hU' : IsOpen U' := hU.preimage e.symm.continuous
    have hc' : IsPreconnected U' := e.symm.toHomeomorph.isPreconnected_preimage.mpr hc
    have hn := analytic_zero_null_connected (volume : Measure (Fin n → ℝ)) hU' hc' hf' hp' he
    let Z' := {x | x ∈ U' ∧ f' x = 0}
    have hZ' : MeasurableSet Z' := by
      have hm : Measurable (U'.piecewise f' (fun _ => 0)) :=
        hf'.continuousOn.measurable_piecewise continuousOn_const hU'.measurableSet
      convert hU'.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
      ext x
      by_cases hx : x ∈ U' <;> simp [Z',hx]
    have hae : ∀ᵐ q ∂(volume : Measure (Fin n → ℝ)).prod volume, q ∈ Z'ᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hn
    have hat := (ae_comp_linearMap_mem_iff e.toLinearMap μ
      ((volume : Measure (Fin n → ℝ)).prod volume) e.surjective hZ'.compl).mpr hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hat] with x hx
    have hx' : e x ∈ Z'ᶜ := hx
    simpa [Z',U',f'] using hx'

end Release061

end

end OAI

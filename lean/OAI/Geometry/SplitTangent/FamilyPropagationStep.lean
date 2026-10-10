import Mathlib
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalTrivialization

namespace OAI

/-! Family Propagation Step. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

structure LocalFamilyTransport (F : ℂ × ℂ → X.Carrier) where
  radius : ℝ
  positive : 0 < radius
  chart_source : ∀ s t, ‖s‖ < radius → ‖t‖ < radius →
    F (s,t) ∈ (chartAt (Model X) (F (0,0))).source
  trans : ℂ → ℂ → ℂ → Model X →L[ℂ] Model X
  normalized : ∀ s u, ‖s‖ < radius → ‖u‖ < radius → trans s u u=1
  cocycle : ∀ s u v w, ‖s‖ < radius → ‖u‖ < radius → ‖v‖ < radius → ‖w‖ < radius →
    trans s v w*trans s u v=trans s u w
  horizontal : ∀ s u v, ‖s‖ < radius → ‖u‖ < radius → ‖v‖ < radius → ∀ e : Model X,
    S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,u))) e=e →
    S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,v))) (trans s u v e)=trans s u v e ∧
    covariantDerivative (S.coordinateProjector (F (0,0)))
      (fun t => (chartAt (Model X) (F (0,0))) (F (s,t))) (fun t => trans s u t e) v=0
  analytic : ∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
    ‖q z‖ < radius → ‖u z‖ < radius → ‖v z‖ < radius →
    AnalyticAt ℂ (fun w => trans (q w) (u w) (v w)) z

 

theorem exists_local_family_transport {F : ℂ × ℂ → X.Carrier}
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) :
    Nonempty (S.LocalFamilyTransport F) := by
  let x := F (0,0)
  let c := chartAt (Model X) x
  have hx : x ∈ c.source := mem_chart_source (Model X) x
  have hxt : c x ∈ c.target := c.map_source hx
  have hf : AnalyticAt ℂ (c ∘ F) (0,0) := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
    exact (hc.comp (0,0) (hF (0,0))).contDiffAt.analyticAt
  obtain ⟨T,r,hr,hT0,_,hTc,hTh,hTa⟩ := exists_horizontal_parameter_transport
    (S.coordinateProjector_analytic x _ hxt) hf (S.coordinateProjector_eventually_idempotent x hxt)
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hF (0,0)).continuousAt (c.open_source.mem_nhds hx))
  let ε := min r q
  have hε : 0 < ε := lt_min hr hq
  have her : ε ≤ r := min_le_left _ _
  have heq : ε ≤ q := min_le_right _ _
  refine ⟨⟨ε,hε,?_,T,?_,?_,?_,?_⟩⟩
  · intro s t hs ht
    apply hqn (s,t)
    simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
    exact max_lt (hs.trans_le heq) (ht.trans_le heq)
  · exact fun s u hs hu => hT0 s u (hs.trans_le her) (hu.trans_le her)
  · exact fun s u v w hs hu hv hw => hTc s u v w (hs.trans_le her) (hu.trans_le her)
      (hv.trans_le her) (hw.trans_le her)
  · exact fun s u v hs hu hv e he => hTh s u v (hs.trans_le her) (hu.trans_le her) (hv.trans_le her) e he
  · exact fun q u v z hq hu hv hqr hur hvr => hTa q u v z hq hu hv
      (hqr.trans_le her) (hur.trans_le her) (hvr.trans_le her)

namespace LocalFamilyTransport
variable {S} {F : ℂ × ℂ → X.Carrier} (L : LocalFamilyTransport S F)
abbrev frame (_L : LocalFamilyTransport S F) := trivializationAt (Model X) (Tangent X) (F (0,0))

 

def map (s u v : ℂ) : Tangent X (F (s,u)) →L[ℂ] Tangent X (F (s,v)) :=
  (L.frame.symmL ℂ (F (s,v))).comp ((L.trans s u v).comp
    ((L.frame.continuousLinearMapAt ℂ (F (s,u))).comp (S.projector (F (s,u)))))

lemma map_self (s u : ℂ) (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius) :
    L.map s u u=S.projector (F (s,u)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [map,ContinuousLinearMap.comp_apply,L.normalized s u hs hu,
    one_apply_eq_self]
  exact L.frame.symmL_continuousLinearMapAt (L.chart_source s u hs hu) _

lemma map_fixed (s u v : ℂ) (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (hv : ‖v‖ < L.radius) (w : Tangent X (F (s,u))) :
    S.projector (F (s,v)) (L.map s u v w)=L.map s u v w := by
  let e := L.frame
  let a := e.continuousLinearMapAt ℂ (F (s,u)) (S.projector (F (s,u)) w)
  have ha : S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,u))) a=a := by
    dsimp only [a,e,frame]
    rw [S.coordinateProjector_fixed _ (L.chart_source s u hs hu),S.idempotent]
  have hh := (L.horizontal s u v hs hu hv a ha).1
  have h := S.coordinateProjector_fixed (F (0,0)) (L.chart_source s v hs hv) (L.map s u v w)
  have ht : e.continuousLinearMapAt ℂ (F (s,v)) (L.map s u v w)=L.trans s u v a := by
    exact e.continuousLinearMapAt_symmL (L.chart_source s v hs hv) _
  change S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,v)))
    (e.continuousLinearMapAt ℂ (F (s,v)) (L.map s u v w))=
    e.continuousLinearMapAt ℂ (F (s,v)) (S.projector (F (s,v)) (L.map s u v w)) at h
  rw [ht,hh] at h
  have h' := congrArg (e.symmL ℂ (F (s,v))) h
  rw [e.symmL_continuousLinearMapAt (L.chart_source s v hs hv)] at h'
  exact h'.symm

end LocalFamilyTransport
end SplitTangent.TangentSplitting

namespace SplitTangent.TangentSplitting.LocalFamilyTransport
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

lemma map_holomorphic_at (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (hqr : ‖q z‖ < L.radius) (hur : ‖u z‖ < L.radius) (hvr : ‖v z‖ < L.radius)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  let t := L.frame
  have hs : F (q z,u z) ∈ t.baseSet := L.chart_source _ _ hqr hur
  have ht : F (q z,v z) ∈ t.baseSet := L.chart_source _ _ hqr hvr
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
    S.holomorphic.contMDiffAt.comp z hσ
  have hc := ((t.contMDiffAt_iff (f := fun w =>
    (⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hs)).mp hp).2
  have hT := L.analytic q u v z hq hu hv hqr hur hvr
  have hprod := hT.contDiffAt.contMDiffAt.clm_apply hc
  apply (t.contMDiffAt_iff (f := fun w =>
    (⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using ht)).mpr
  have hbase : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun w => F (q w,v w)) z :=
    (hF (q z,v z)).comp z (f := fun w => (q w,v w)) (hq.prod hv).contDiffAt.contMDiffAt
  refine ⟨hbase,?_⟩
  apply hprod.congr_of_eventuallyEq
  filter_upwards [hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqr)),
    hu.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hur)),
    hv.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hvr))] with w hqw huw hvw
  have hsu : F (q w,u w) ∈ t.baseSet := L.chart_source _ _
    (mem_ball_zero_iff.mp hqw) (mem_ball_zero_iff.mp huw)
  have hsv : F (q w,v w) ∈ t.baseSet := L.chart_source _ _
    (mem_ball_zero_iff.mp hqw) (mem_ball_zero_iff.mp hvw)
  change (t ⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩).2 =
    L.trans (q w) (u w) (v w) (t ⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hsv,
    ← t.continuousLinearMapAt_apply_of_mem ℂ hsu]
  exact t.continuousLinearMapAt_symmL hsv _

end

section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

lemma map_projector (s u v : ℂ) :
    (L.map s u v).comp (S.projector (F (s,u))) = L.map s u v := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply,map,S.idempotent]

 

lemma map_cocycle (s u v w : ℂ) (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (hv : ‖v‖ < L.radius) (hw : ‖w‖ < L.radius) :
    (L.map s v w).comp (L.map s u v) = L.map s u w := by
  apply ContinuousLinearMap.ext
  intro a
  change L.frame.symmL ℂ (F (s,w))
      (L.trans s v w (L.frame.continuousLinearMapAt ℂ (F (s,v))
        (S.projector (F (s,v)) (L.map s u v a)))) = _
  rw [L.map_fixed s u v hs hu hv]
  have he : L.frame.continuousLinearMapAt ℂ (F (s,v)) (L.map s u v a) =
      L.trans s u v (L.frame.continuousLinearMapAt ℂ (F (s,u)) (S.projector (F (s,u)) a)) :=
    L.frame.continuousLinearMapAt_symmL (L.chart_source s v hs hv) _
  rw [he]
  change L.frame.symmL ℂ (F (s,w))
      ((L.trans s v w * L.trans s u v)
        (L.frame.continuousLinearMapAt ℂ (F (s,u)) (S.projector (F (s,u)) a))) = _
  rw [L.cocycle s u v w hs hu hv hw]
  rfl

 

lemma map_reverse_comp (s u v : ℂ) (hs : ‖s‖ < L.radius)
    (hu : ‖u‖ < L.radius) (hv : ‖v‖ < L.radius) :
    (L.map s v u).comp (L.map s u v) = S.projector (F (s,u)) := by
  rw [L.map_cocycle s u v u hs hu hv hu,L.map_self s u hs hu]

end

section
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

theorem map_eq_of_horizontal_germ
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {s u : ℂ} (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (σ : ∀ t, Tangent X (F (s,t)))
    (hσ : AnalyticAt ℂ
      (fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)) u)
    (hfix : ∀ᶠ t in 𝓝 u, S.projector (F (s,t)) (σ t)=σ t)
    (hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (F (0,0)))
        (fun v => (chartAt (Model X) (F (0,0))) (F (s,v)))
        (fun v => L.frame.continuousLinearMapAt ℂ (F (s,v)) (σ v)) t=0) :
    (fun t => L.map s u t (σ u)) =ᶠ[𝓝 u] σ := by
  let c := chartAt (Model X) (F (0,0))
  let P := S.coordinateProjector (F (0,0))
  let g : ℂ → Model X := fun t => c (F (s,t))
  let e := L.frame.continuousLinearMapAt ℂ (F (s,u)) (σ u)
  let f : ℂ → Model X := fun t => L.trans s u t e
  let h : ℂ → Model X := fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)
  have hsource : F (s,u) ∈ c.source := L.chart_source s u hs hu
  have hP : AnalyticAt ℂ P (g u) :=
    S.coordinateProjector_analytic (F (0,0)) _ (c.map_source hsource)
  have hg : AnalyticAt ℂ g u := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F (0,0))) hsource
    have hk : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) ω (fun t : ℂ => (s,t)) u :=
      (contDiff_const.prodMk contDiff_id).contDiffAt.contMDiffAt
    exact (hc.comp u ((hF (s,u)).comp u hk)).contDiffAt.analyticAt
  have he : P (g u) e=e := by
    dsimp only [P,g,e,frame]
    rw [S.coordinateProjector_fixed _ hsource,hfix.self_of_nhds]
  have hn : ∀ᶠ t in 𝓝 u, ‖t‖ < L.radius := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht
    exact mem_ball_zero_iff.mp ht
  have hfa (t : ℂ) (ht : ‖t‖ < L.radius) : AnalyticAt ℂ f t := by
    exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp
      (analyticAt_const.prod (L.analytic (fun _ => s) (fun _ => u) id t analyticAt_const analyticAt_const
        analyticAt_id hs hu ht))
  have hfd : ∀ᶠ t in 𝓝 u, DifferentiableAt ℂ f t ∧ covariantDerivative P g f t=0 := by
    filter_upwards [hn] with t ht
    exact ⟨(hfa t ht).differentiableAt,(L.horizontal s u t hs hu ht e he).2⟩
  have hhd : ∀ᶠ t in 𝓝 u, DifferentiableAt ℂ h t ∧ covariantDerivative P g h t=0 := by
    filter_upwards [hσ.eventually_analyticAt,hh] with t ht hht
    exact ⟨ht.differentiableAt,hht⟩
  have hfi : ∀ᶠ t in 𝓝 u, P (g t) (f t)=f t := by
    filter_upwards [hn] with t ht
    exact (L.horizontal s u t hs hu ht e he).1
  have hhi : ∀ᶠ t in 𝓝 u, P (g t) (h t)=h t := by
    filter_upwards [hn,hfix] with t ht hft
    dsimp only [P,g,h,frame]
    rw [S.coordinateProjector_fixed _ (L.chart_source s t hs ht),hft]
  have hinit : f u=h u := by
    dsimp only [f,h,e]
    rw [L.normalized s u hs hu]
    rfl
  have heq := horizontal_local_uniqueness hP hg
    (S.coordinateProjector_eventually_idempotent (F (0,0)) (c.map_source hsource))
    hfd hhd hfi hhi hinit
  filter_upwards [heq,hn] with t ht htn
  change L.frame.symmL ℂ (F (s,t))
    (L.trans s u t (L.frame.continuousLinearMapAt ℂ (F (s,u))
      (S.projector (F (s,u)) (σ u))))=σ t
  rw [hfix.self_of_nhds]
  change L.frame.symmL ℂ (F (s,t)) (f t)=σ t
  rw [ht]
  exact L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs htn) _

end

open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

theorem map_eq_on_ball_of_horizontal_germ
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {s u : ℂ} (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (σ : ∀ t, Tangent X (F (s,t)))
    (hσ : AnalyticOnNhd ℂ
      (fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)) (Metric.ball 0 L.radius))
    (hfix : ∀ᶠ t in 𝓝 u, S.projector (F (s,t)) (σ t)=σ t)
    (hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (F (0,0)))
        (fun v => (chartAt (Model X) (F (0,0))) (F (s,v)))
        (fun v => L.frame.continuousLinearMapAt ℂ (F (s,v)) (σ v)) t=0) :
    ∀ t, ‖t‖ < L.radius → L.map s u t (σ u)=σ t := by
  let e := L.frame.continuousLinearMapAt ℂ (F (s,u)) (σ u)
  let f : ℂ → Model X := fun t => L.trans s u t e
  let h : ℂ → Model X := fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)
  have he (t : ℂ) (ht : ‖t‖ < L.radius) :
      L.frame.continuousLinearMapAt ℂ (F (s,t)) (L.map s u t (σ u)) = f t := by
    change L.frame.continuousLinearMapAt ℂ (F (s,t))
      (L.frame.symmL ℂ (F (s,t)) (L.trans s u t
        (L.frame.continuousLinearMapAt ℂ (F (s,u)) (S.projector (F (s,u)) (σ u)))))=f t
    rw [hfix.self_of_nhds]
    exact L.frame.continuousLinearMapAt_symmL (L.chart_source s t hs ht) _
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 L.radius) := by
    intro t ht
    exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp
      (analyticAt_const.prod (L.analytic (fun _ => s) (fun _ => u) id t analyticAt_const analyticAt_const
        analyticAt_id hs hu (mem_ball_zero_iff.mp ht)))
  have hgerm := L.map_eq_of_horizontal_germ hF hs hu σ
    (hσ u (mem_ball_zero_iff.mpr hu)) hfix hh
  have hfg : f =ᶠ[𝓝 u] h := by
    filter_upwards [hgerm,Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht htr
    exact (he t (mem_ball_zero_iff.mp htr)).symm.trans
      (congrArg (L.frame.continuousLinearMapAt ℂ (F (s,t))) ht)
  have hall := hf.eqOn_of_preconnected_of_eventuallyEq hσ
    (convex_ball (0 : ℂ) L.radius).isPreconnected (mem_ball_zero_iff.mpr hu) hfg
  intro t ht
  have heq := (he t ht).trans (hall (mem_ball_zero_iff.mpr ht))
  have h := congrArg (L.frame.symmL ℂ (F (s,t))) heq
  rw [L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs ht),
    L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs ht)] at h
  exact h

end SplitTangent.TangentSplitting.LocalFamilyTransport

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma coordinate_covariantDerivative_change {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) = 0)
    (σ : ∀ z, Tangent X (g z)) (x y : X.Carrier) {z : ℂ}
    (hx : g z ∈ (chartAt (Model X) x).source)
    (hy : g z ∈ (chartAt (Model X) y).source)
    (hσ : AnalyticAt ℂ (fun w =>
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)) z) :
    covariantDerivative (S.coordinateProjector y) ((chartAt (Model X) y) ∘ g)
      (fun w => (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (g w) (σ w)) z =
    fderiv ℂ (coordinateTransition x y) ((chartAt (Model X) x) (g z))
      (covariantDerivative (S.coordinateProjector x) ((chartAt (Model X) x) ∘ g)
        (fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)) z) := by
  let c := chartAt (Model X) x
  let d := chartAt (Model X) y
  let φ := coordinateTransition x y
  let P := S.coordinateProjector x
  let Q := S.coordinateProjector y
  let f := fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)
  let h := fun w => (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (g w) (σ w)
  have he : c.symm (c (g z)) = g z := c.left_inv hx
  have hφ : φ (c (g z)) = d (g z) := by
    change d (c.symm (c (g z))) = d (g z)
    rw [he]
  have hnat : ∀ᶠ a in 𝓝 (c (g z)), ∀ v : Model X,
      Q (φ a) (fderiv ℂ φ a v) = fderiv ℂ φ a (P a v) := by
    have hcn : ContinuousAt c.symm (c (g z)) := c.continuousAt_symm (c.map_source hx)
    have hn : ∀ᶠ a in 𝓝 (c (g z)), c.symm a ∈ d.source :=
      hcn (d.open_source.mem_nhds (by rw [he]; exact hy))
    filter_upwards [c.open_target.mem_nhds (c.map_source hx),hn] with a ha ha'
    intro v
    exact (congrArg (fun A : Model X →L[ℂ] Model X => A v)
      (S.coordinateProjector_intertwining x y ha ha')).symm
  have hnA : ∀ᶠ w in 𝓝 z, g w ∈ c.source := (hg z).continuousAt (c.open_source.mem_nhds hx)
  have hnB : ∀ᶠ w in 𝓝 z, g w ∈ d.source := (hg z).continuousAt (d.open_source.mem_nhds hy)
  have hcurve : φ ∘ (c ∘ g) =ᶠ[𝓝 z] d ∘ g := by
    filter_upwards [hnA] with w hw
    change d (c.symm (c (g w))) = d (g w)
    rw [c.left_inv hw]
  have hsection : (fun w => fderiv ℂ φ ((c ∘ g) w) (f w)) =ᶠ[𝓝 z] h := by
    filter_upwards [hnA,hnB] with w hw hw'
    have hei : c.symm (c (g w)) = g w := c.left_inv hw
    have hd := coordinateTransition_derivative x y (c.map_source hw) (by rw [hei]; exact hw')
    rw [hei] at hd
    change fderiv ℂ (coordinateTransition x y) (c (g w)) (f w) = h w
    rw [hd]
    dsimp only [ContinuousLinearMap.comp_apply,f,h]
    rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hw]
  have hq : DifferentiableAt ℂ Q (φ ((c ∘ g) z)) := by
    rw [show (c ∘ g) z = c (g z) from rfl,hφ]
    exact (S.coordinateProjector_analytic y _ (d.map_source hy)).differentiableAt
  have hid : ∀ w : Model X, Q (φ ((c ∘ g) z)) (Q (φ ((c ∘ g) z)) w) = Q (φ ((c ∘ g) z)) w := by
    rw [show (c ∘ g) z = c (g z) from rfl,hφ]
    exact S.coordinateProjector_idempotent y (d.map_source hy)
  have hn := covariantDerivative_naturality
    (S.coordinateProjector_analytic x _ (c.map_source hx)).differentiableAt hq
    (coordinateTransition_analytic x y (c.map_source hx) (by
      change c.symm (c (g z)) ∈ d.source
      rw [he]; exact hy))
    (coordinateCurve_analytic hg x hx).differentiableAt hσ.differentiableAt hnat
    (S.coordinateCurve_complementary hg hv x hx) hid
  rw [covariantDerivative_curve_congr hcurve,covariantDerivative_congr hsection] at hn
  exact hn

end SplitTangent.TangentSplitting

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

lemma continuationMap_horizontal (a z : ℂ) (v : Tangent X (g a)) (x : X.Carrier)
    (hx : g z ∈ (chartAt (Model X) x).source) :
    covariantDerivative (S.coordinateProjector x) ((chartAt (Model X) x) ∘ g)
      (fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w)
        (L.continuationMap hg hv a w v)) z = 0 := by
  let v₀ : TangentImageFiber S g a := ⟨S.projector (g a) v,S.idempotent _ v⟩
  let v₁ := L.continuation hg hv a z v₀
  let σ := fun w => L.continuationMap hg hv a w v
  let f := fun w => L.coords z w (σ w)
  let h := fun w => L.trans z z w (L.coords z z v₁)
  have hfe : f =ᶠ[𝓝 z] h := by
    filter_upwards [L.continuation_germ hg hv a z v₀,
      Metric.ball_mem_nhds z (L.positive z)] with w hw hw'
    dsimp only [f,σ]
    rw [L.continuationMap_apply]
    change L.coords z w (L.continuation hg hv a w v₀).1 = h w
    rw [hw,L.forward_val hw',L.coords_uncoords hw']
  have hfa : AnalyticAt ℂ f z :=
    (L.trans_analytic (L.center z) (L.center z) (L.coords z z v₁)).congr hfe.symm
  have hh : covariantDerivative (S.coordinateProjector (g z)) ((chartAt (Model X) (g z)) ∘ g) f z = 0 := by
    rw [covariantDerivative_congr hfe]
    exact (L.horizontal z z (L.center z) z (L.center z) _ (L.coords_fixed (L.center z) v₁)).2
  have he := S.coordinate_covariantDerivative_change hg hv σ (g z) x
    (L.chart_source z z (L.center z)) hx hfa
  rw [hh,map_zero] at he
  exact he

 

lemma continuationMap_coordinates_analytic (a z : ℂ) (v : Tangent X (g a)) (x : X.Carrier)
    (hx : g z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ (fun w =>
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w)
        (L.continuationMap hg hv a w v)) z := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hc := ((t.contMDiffAt_iff (f := fun w =>
    (⟨g w,L.continuationMap hg hv a w v⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
    (t.mem_source.mpr (show g z ∈ t.baseSet from hx))).mp (L.continuationMap_holomorphic hg hv a v z)).2
  apply hc.contDiffAt.analyticAt.congr
  filter_upwards [(hg z).continuousAt ((chartAt (Model X) x).open_source.mem_nhds hx)] with w hw
  exact (t.continuousLinearMapAt_apply_of_mem ℂ hw _).symm

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting.LocalFamilyTransport
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

lemma map_eq_continuationMap
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    (s : ℂ) (K : LocalChartImages S (fun t => F (s,t)))
    (hslice : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun t => F (s,t)))
    (hvel : ∀ t, S.projector (F (s,t))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => F (s,z)) t (1 : ℂ))=0)
    (u v : ℂ) (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius) (hv : ‖v‖ < L.radius) :
    L.map s u v = K.continuationMap hslice hvel u v := by
  apply ContinuousLinearMap.ext
  intro e
  let σ := fun t => K.continuationMap hslice hvel u t e
  have hσ : AnalyticOnNhd ℂ (fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t))
      (Metric.ball 0 L.radius) := by
    intro t ht
    exact K.continuationMap_coordinates_analytic hslice hvel u t e (F (0,0))
      (L.chart_source s t hs (mem_ball_zero_iff.mp ht))
  have hn : ∀ᶠ t in 𝓝 u, ‖t‖ < L.radius := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht
    exact mem_ball_zero_iff.mp ht
  have hfix : ∀ᶠ t in 𝓝 u, S.projector (F (s,t)) (σ t) = σ t :=
    Filter.Eventually.of_forall fun t => K.continuationMap_fixed hslice hvel u t e
  have hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (F (0,0)))
        (fun z => (chartAt (Model X) (F (0,0))) (F (s,z)))
        (fun z => L.frame.continuousLinearMapAt ℂ (F (s,z)) (σ z)) t = 0 := by
    filter_upwards [hn] with t ht
    exact K.continuationMap_horizontal hslice hvel u t e (F (0,0)) (L.chart_source s t hs ht)
  have he := L.map_eq_on_ball_of_horizontal_germ hF hs hu σ hσ hfix hh v hv
  have hinit : σ u = S.projector (F (s,u)) e := by
    change K.continuationMap hslice hvel u u e = _
    rw [K.continuationMap_self]
  rw [hinit] at he
  have hp := congrArg (fun A : Tangent X (F (s,u)) →L[ℂ] Tangent X (F (s,v)) => A e)
    (L.map_projector s u v)
  exact hp.symm.trans he

end SplitTangent.TangentSplitting.LocalFamilyTransport

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {F : ℂ × ℂ → X.Carrier}

lemma family_slice_holomorphic
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) (s : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun t => F (s,t)) :=
  hF.comp (contDiff_const.prodMk contDiff_id).contMDiff

abbrev shiftedFamily (F : ℂ × ℂ → X.Carrier) (s₀ t₀ : ℂ) : ℂ × ℂ → X.Carrier :=
  fun p => F (s₀+p.1,t₀+p.2)

lemma shiftedFamily_holomorphic
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) (s₀ t₀ : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (shiftedFamily F s₀ t₀) :=
  hF.comp ((contDiff_const.add contDiff_fst).prodMk (contDiff_const.add contDiff_snd)).contMDiff

variable (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
  (hvel : ∀ s t, S.projector (F (s,t))
    (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => F (s,z)) t (1 : ℂ))=0)
  (K : ∀ s, LocalChartImages S (fun t => F (s,t)))

 

abbrev familyContinuation (s a b : ℂ) : Tangent X (F (s,a)) →L[ℂ] Tangent X (F (s,b)) :=
  (K s).continuationMap (family_slice_holomorphic hF s) (hvel s) a b

namespace LocalFamilyTransport
lemma map_eq_familyContinuation_shift (s₀ t₀ : ℂ)
    (L : LocalFamilyTransport S (shiftedFamily F s₀ t₀)) (s u v : ℂ)
    (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius) (hv : ‖v‖ < L.radius) :
    L.map s u v = familyContinuation hF hvel K (s₀+s) (t₀+u) (t₀+v) := by
  apply ContinuousLinearMap.ext
  intro e
  let k : ℂ → ℂ := fun t => t₀+t
  let σ := fun t => familyContinuation hF hvel K (s₀+s) (t₀+u) (k t) e
  have hsrc (t : ℂ) (ht : ‖t‖ < L.radius) :
      F (s₀+s,k t) ∈ (chartAt (Model X) (shiftedFamily F s₀ t₀ (0,0))).source := by
    simpa only [shiftedFamily,σ,familyContinuation,k,frame] using L.chart_source s t hs ht
  have hσ : AnalyticOnNhd ℂ (fun t => L.frame.continuousLinearMapAt ℂ
      (shiftedFamily F s₀ t₀ (s,t)) (σ t)) (Metric.ball 0 L.radius) := by
    intro t ht
    have hc := ((K (s₀+s)).continuationMap_coordinates_analytic (family_slice_holomorphic hF (s₀+s))
      (hvel (s₀+s)) (t₀+u) (k t) e (shiftedFamily F s₀ t₀ (0,0))
      (hsrc t (mem_ball_zero_iff.mp ht))).comp (analyticAt_const.add analyticAt_id)
    simpa only [shiftedFamily,σ,familyContinuation,k,frame,Function.comp_def] using hc
  have hfix : ∀ᶠ t in 𝓝 u,
      S.projector (shiftedFamily F s₀ t₀ (s,t)) (σ t) = σ t := by
    filter_upwards [] with t
    simpa only [shiftedFamily,σ,familyContinuation,k,frame] using
      (K (s₀+s)).continuationMap_fixed (family_slice_holomorphic hF (s₀+s)) (hvel (s₀+s)) (t₀+u) (k t) e
  have hn : ∀ᶠ t in 𝓝 u, ‖t‖ < L.radius := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht
    exact mem_ball_zero_iff.mp ht
  have hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (shiftedFamily F s₀ t₀ (0,0)))
        (fun z => (chartAt (Model X) (shiftedFamily F s₀ t₀ (0,0)))
          (shiftedFamily F s₀ t₀ (s,z)))
        (fun z => L.frame.continuousLinearMapAt ℂ (shiftedFamily F s₀ t₀ (s,z)) (σ z)) t=0 := by
    filter_upwards [hn] with t ht
    let x := shiftedFamily F s₀ t₀ (0,0)
    have hc := (K (s₀+s)).continuationMap_coordinates_analytic (family_slice_holomorphic hF (s₀+s))
      (hvel (s₀+s)) (t₀+u) (k t) e x (hsrc t ht)
    have hg := coordinateCurve_analytic (family_slice_holomorphic hF (s₀+s)) x (hsrc t ht)
    have he := covariantDerivative_reparam (P := S.coordinateProjector x)
      hg.differentiableAt hc.differentiableAt ((analyticAt_const.add analyticAt_id).differentiableAt)
    rw [(K (s₀+s)).continuationMap_horizontal (family_slice_holomorphic hF (s₀+s)) (hvel (s₀+s))
      (t₀+u) (k t) e x (hsrc t ht),smul_zero] at he
    simpa only [shiftedFamily,σ,familyContinuation,k,frame,Function.comp_def,x] using he
  have he := L.map_eq_on_ball_of_horizontal_germ (shiftedFamily_holomorphic hF s₀ t₀)
    hs hu σ hσ hfix hh v hv
  have hinit : σ u = S.projector (F (s₀+s,t₀+u)) e := by
    change (K (s₀+s)).continuationMap _ _ (t₀+u) (t₀+u) e = _
    rw [(K (s₀+s)).continuationMap_self]
  rw [hinit] at he
  have hp := congrArg (fun A : Tangent X (F (s₀+s,t₀+u)) →L[ℂ] Tangent X (F (s₀+s,t₀+v)) => A e)
    (L.map_projector s u v)
  simp only [shiftedFamily,ContinuousLinearMap.comp_apply] at hp
  simpa only [σ,familyContinuation,k] using hp.symm.trans he

lemma familyContinuation_holomorphic_at_local (s₀ t₀ : ℂ)
    (L : LocalFamilyTransport S (shiftedFamily F s₀ t₀))
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (hqr : ‖q z-s₀‖ < L.radius) (hur : ‖u z-t₀‖ < L.radius)
    (hvr : ‖v z-t₀‖ < L.radius)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),familyContinuation hF hvel K (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  have hadd (a b : ℂ) : a+(b-a)=b := by ring
  let q' := fun w => q w-s₀
  let u' := fun w => u w-t₀
  let v' := fun w => v w-t₀
  have hσ' : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨shiftedFamily F s₀ t₀ (q' w,u' w),σ w⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
    convert hσ using 1
    funext w
    dsimp only [shiftedFamily,q',u']
    erw [hadd,hadd]
  have h := L.map_holomorphic_at (shiftedFamily_holomorphic hF s₀ t₀)
    (hq.sub analyticAt_const) (hu.sub analyticAt_const) (hv.sub analyticAt_const)
    hqr hur hvr (fun w => σ w) hσ'
  have hqr' : ∀ᶠ w in 𝓝 z, ‖q' w‖ < L.radius :=
    (hq.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hqr)
  have hur' : ∀ᶠ w in 𝓝 z, ‖u' w‖ < L.radius :=
    (hu.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hur)
  have hvr' : ∀ᶠ w in 𝓝 z, ‖v' w‖ < L.radius :=
    (hv.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hvr)
  apply h.congr_of_eventuallyEq
  filter_upwards [hqr',hur',hvr'] with w hwq hwu hwv
  dsimp only [Pi.sub_apply]
  erw [L.map_eq_familyContinuation_shift hF hvel K s₀ t₀ (q' w) (u' w) (v' w) hwq hwu hwv]
  dsimp only [shiftedFamily,q',u',v']
  erw [hadd,hadd,hadd]
  rfl

end LocalFamilyTransport

lemma familyContinuation_cocycle (s a b c : ℂ) (e : Tangent X (F (s,a))) :
    familyContinuation hF hvel K s b c (familyContinuation hF hvel K s a b e) =
      familyContinuation hF hvel K s a c e :=
  (K s).continuationMap_cocycle (family_slice_holomorphic hF s) (hvel s) a b c e

 

lemma familyContinuation_holomorphic_at_const_end
    {q u : ℂ → ℂ} {z : ℂ} (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z)
    (b : ℂ) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,b),familyContinuation hF hvel K (q w) (u w) b (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  let Good : Set ℂ := {b | ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,b),familyContinuation hF hvel K (q w) (u w) b (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z}
  have spread (b : ℂ) : ∃ r : ℝ, 0 < r ∧ ∀ b₁ ∈ Metric.ball b r,
      ∀ b₂ ∈ Metric.ball b r, b₁ ∈ Good → b₂ ∈ Good := by
    obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) b)
    refine ⟨L.radius,L.positive,?_⟩
    intro b₁ hb₁ b₂ hb₂ h₁
    have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    have h₁' : ‖b₁-b‖ < L.radius := by simpa only [Metric.mem_ball,dist_eq_norm] using hb₁
    have h₂' : ‖b₂-b‖ < L.radius := by simpa only [Metric.mem_ball,dist_eq_norm] using hb₂
    have ht := L.familyContinuation_holomorphic_at_local hF hvel K (q z) b
      hq analyticAt_const analyticAt_const hq0 h₁' h₂'
      (fun w => familyContinuation hF hvel K (q w) (u w) b₁ (σ w)) h₁
    change ContMDiffAt _ _ _ _ _
    apply ht.congr_of_eventuallyEq
    filter_upwards [] with w
    rw [familyContinuation_cocycle]
  have hg : Good.Nonempty := by
    obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) (u z))
    have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    have hu0 : ‖u z-u z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    exact ⟨u z,L.familyContinuation_holomorphic_at_local hF hvel K (q z) (u z)
      hq hu analyticAt_const hq0 hu0 hu0 σ hσ⟩
  have ho : IsOpen Good := isOpen_iff_mem_nhds.mpr fun b hb => by
    obtain ⟨r,hr,hs⟩ := spread b
    apply Filter.mem_of_superset (Metric.ball_mem_nhds b hr)
    intro b' hb'
    exact hs b (Metric.mem_ball_self hr) b' hb' hb
  have hc : IsOpen Goodᶜ := isOpen_iff_mem_nhds.mpr fun b hb => by
    obtain ⟨r,hr,hs⟩ := spread b
    apply Filter.mem_of_superset (Metric.ball_mem_nhds b hr)
    intro b' hb' hgood
    exact hb (hs b' hb' b (Metric.mem_ball_self hr) hgood)
  have he : Good = Set.univ := IsClopen.eq_univ (⟨isOpen_compl_iff.mp hc,ho⟩ : IsClopen Good) hg
  have hb : b ∈ Good := by rw [he]; trivial
  exact hb

 

theorem familyContinuation_holomorphic_at
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),familyContinuation hF hvel K (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) (v z))
  have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
  have hv0 : ‖v z-v z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
  have ht := L.familyContinuation_holomorphic_at_local hF hvel K (q z) (v z)
    hq analyticAt_const hv hq0 hv0 hv0
    (fun w => familyContinuation hF hvel K (q w) (u w) (v z) (σ w))
    (familyContinuation_holomorphic_at_const_end hF hvel K hq hu σ hσ (v z))
  apply ht.congr_of_eventuallyEq
  filter_upwards [] with w
  rw [familyContinuation_cocycle]

end SplitTangent.TangentSplitting

end

end OAI

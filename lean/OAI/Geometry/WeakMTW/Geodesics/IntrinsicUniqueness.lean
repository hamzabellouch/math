import Mathlib
import OAI.Geometry.WeakMTW.Model
import OAI.Geometry.WeakMTW.Coordinates.IntrinsicNormal

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem coordinate_germ_unique (x : M) {U : Set ℝ} (hU : IsOpen U)
    {c d : ℝ → E} (hc : ContDiffOn ℝ ∞ c U) (hd : ContDiffOn ℝ ∞ d U)
    (hct : ∀ t ∈ U, c t ∈ (chartAt E x).target)
    (hdt : ∀ t ∈ U, d t ∈ (chartAt E x).target)
    {a C D : ℝ} (ha : a ∈ U) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (c s)) ((chartAt E x).symm (c t)) = C * |s - t|)
    (hdDist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (d s)) ((chartAt E x).symm (d t)) = D * |s - t|)
    (he : c a = d a) (he' : deriv c a = deriv d a) : c =ᶠ[𝓝 a] d := by
  obtain ⟨N⟩ := exists_normalFlow (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) (hct a ha)
  obtain ⟨δ, hδ, _, hδs⟩ := intrinsic_curve_normal x hU hc hct ha hC hcDist N N.center_mem
  obtain ⟨ε, hε, _, hεs⟩ := intrinsic_curve_normal x hU hd hdt ha hD hdDist N
    (by rw [← he]; exact N.center_mem)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ),
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with t htδ htε
  rw [hδs t htδ, hεs t htε, ← he, he']

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

def curveState (γ : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, E) M :=
  ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩

 theorem curveState_continuous {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ) :
    Continuous (curveState (E := E) γ) := by
  have h := hγ.continuous_tangentMap (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hs : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  exact h.comp hs

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
 theorem curveState_congr {γ η : ℝ → M} {a : ℝ} (h : γ =ᶠ[𝓝 a] η) :
    curveState (E := E) γ a = curveState (E := E) η a := by
  refine TotalSpace.ext h.eq_of_nhds ?_
  apply heq_of_eq
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η a (1 : ℝ)
  rw [h.mfderiv_eq]
  rfl

 theorem curveState_chart_deriv (x : M) {γ : ℝ → M} {a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a)
    (ha : γ a ∈ (chartAt E x).source) :
    deriv ((chartAt E x) ∘ γ) a =
      (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) (curveState (E := E) γ a)).2 := by
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
  rw [mfderiv_comp a (mdifferentiableAt_atlas (chart_mem_atlas E x) ha) hγ]
  rfl

end

 theorem intrinsic_germ_unique {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {a C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (γ s) (γ t) = C * |s - t|)
    (hdDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (η s) (η t) = D * |s - t|)
    (he : curveState (E := E) γ a = curveState (E := E) η a) : γ =ᶠ[𝓝 a] η := by
  let x := γ a
  let e := chartAt E x
  have hpoint : γ a = η a := congrArg TotalSpace.proj he
  have hγa : γ a ∈ e.source := mem_chart_source E (γ a)
  have hηa : η a ∈ e.source := by rw [← hpoint]; exact hγa
  obtain ⟨ε, hε, hcs⟩ := hcDist
  obtain ⟨δ, hδ, hds⟩ := hdDist
  let U : Set ℝ := Metric.ball a ε ∩ Metric.ball a δ ∩
    (γ ⁻¹' e.source ∩ η ⁻¹' e.source)
  have hU : IsOpen U := (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    ((e.open_source.preimage hγ.continuous).inter (e.open_source.preimage hη.continuous))
  have ha : a ∈ U := ⟨⟨Metric.mem_ball_self hε, Metric.mem_ball_self hδ⟩, hγa, hηa⟩
  let c : ℝ → E := e ∘ γ
  let d : ℝ → E := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hγ.contMDiffOn (fun t ht => ht.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hη.contMDiffOn (fun t ht => ht.2.2))
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2
  have he' : deriv c a = deriv d a := by
    rw [curveState_chart_deriv x (hγ.mdifferentiable (by simp) a) hγa,
      curveState_chart_deriv x (hη.mdifferentiable (by simp) a) hηa, he]
  have hh := coordinate_germ_unique x hU hc hd hct hdt ha hC hD
    (fun s hs t ht => by
      change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
      rw [e.left_inv hs.2.1, e.left_inv ht.2.1]
      exact hcs s hs.1.1 t ht.1.1)
    (fun s hs t ht => by
      change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
      rw [e.left_inv hs.2.2, e.left_inv ht.2.2]
      exact hds s hs.1.2 t ht.1.2)
    (congrArg e hpoint) he'
  filter_upwards [hh, hU.mem_nhds ha] with t ht htU
  have hh' := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh'
  rwa [e.left_inv htU.2.1, e.left_inv htU.2.2] at hh'

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem tangentBundle_t2Space : T2Space (TangentBundle 𝓘(ℝ, E) M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hb : p.proj = q.proj
  · let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ, E) x) p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := e.mem_source.mpr (by
      rw [← hb]
      exact mem_baseSet_trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ, E) x) p.proj)
    have he : e p ≠ e q := fun h => hpq (e.toOpenPartialHomeomorph.injOn hp hq h)
    exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr he).mono
      (e.toOpenPartialHomeomorph.continuousAt hp) (e.toOpenPartialHomeomorph.continuousAt hq))
  · exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr hb).mono
      (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ, E) x)).continuousAt
      (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ, E) x)).continuousAt)

 theorem intrinsic_global_unique {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∀ a, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (γ s) (γ t) = C * |s - t|)
    (hdDist : ∀ a, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (η s) (η t) = D * |s - t|)
    {a : ℝ} (he : curveState (E := E) γ a = curveState (E := E) η a) : γ = η := by
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  let A : Set ℝ := {t | curveState (E := E) γ t = curveState (E := E) η t}
  have hclosed : IsClosed A := isClosed_eq (curveState_continuous hγ) (curveState_continuous hη)
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hg := intrinsic_germ_unique hγ hη hC hD (hcDist t) (hdDist t) ht
    exact hg.eventuallyEq_nhds.mono (fun s hs => curveState_congr hs)
  have huniv : A = univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨a, he⟩
  funext t
  have h : t ∈ A := by rw [huniv]; exact mem_univ t
  exact congrArg TotalSpace.proj h
end
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem completeGeodesic_unique {x : M} {v : TangentSpace (model n) x} {γ η : ℝ → M}
    (hγ : CompleteGeodesicWithInitialData x v γ)
    (hη : CompleteGeodesicWithInitialData x v η) : γ = η := by
  obtain ⟨hγs, hγx, hγv, hγd⟩ := hγ
  obtain ⟨hηs, hηx, hηv, hηd⟩ := hη
  apply intrinsic_global_unique hγs hηs (norm_nonneg v) (norm_nonneg v) hγd hηd
    (a := 0)
  refine TotalSpace.ext (hγx.trans hηx.symm) ?_
  dsimp only [curveState]
  exact (eqRec_heq_iff.mp (heq_of_eq hγv)).trans
    (eqRec_heq_iff.mp (heq_of_eq hηv)).symm
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

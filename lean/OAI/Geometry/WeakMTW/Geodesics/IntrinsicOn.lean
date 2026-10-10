import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicUniqueness

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

 theorem intrinsic_germ_unique_on {V : Set ℝ} (hV : IsOpen V) {γ η : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ V)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η V)
    {a C D : ℝ} (haV : a ∈ V) (hC : 0 ≤ C) (hD : 0 ≤ D)
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
  let U : Set ℝ := V ∩ (Metric.ball a ε ∩ Metric.ball a δ ∩
    (γ ⁻¹' e.source ∩ η ⁻¹' e.source))
  have hU : IsOpen U := by
    have hc := hγ.continuousOn.isOpen_inter_preimage hV e.open_source
    have hd := hη.continuousOn.isOpen_inter_preimage hV e.open_source
    convert! (hc.inter hd).inter ((Metric.isOpen_ball (x := a) (ε := ε)).inter (Metric.isOpen_ball (x := a) (ε := δ))) using 1
    ext t
    simp only [U, mem_inter_iff, mem_preimage]
    tauto
  have ha : a ∈ U := ⟨haV, ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hδ⟩, hγa, hηa⟩
  let c : ℝ → E := e ∘ γ
  let d : ℝ → E := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp (hγ.mono inter_subset_left) (fun t ht => ht.2.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp (hη.mono inter_subset_left) (fun t ht => ht.2.2.2))
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2.2
  have he' : deriv c a = deriv d a := by
    rw [curveState_chart_deriv x (((hγ a haV).contMDiffAt (hV.mem_nhds haV)).mdifferentiableAt (by simp)) hγa,
      curveState_chart_deriv x (((hη a haV).contMDiffAt (hV.mem_nhds haV)).mdifferentiableAt (by simp)) hηa, he]
  have hh := coordinate_germ_unique x hU hc hd hct hdt ha hC hD
    (fun s hs t ht => by
      change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
      rw [e.left_inv hs.2.2.1, e.left_inv ht.2.2.1]
      exact hcs s hs.2.1.1 t ht.2.1.1)
    (fun s hs t ht => by
      change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
      rw [e.left_inv hs.2.2.2, e.left_inv ht.2.2.2]
      exact hds s hs.2.1.2 t ht.2.1.2)
    (congrArg e hpoint) he'
  filter_upwards [hh, hU.mem_nhds ha] with t ht htU
  have hh' := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh'
  rwa [e.left_inv htU.2.2.1, e.left_inv htU.2.2.2] at hh'

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

theorem curveState_continuousOn {U : Set ℝ} (hU : IsOpen U) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ U) :
    ContinuousOn (curveState (E := E) γ) U := by
  have h := hγ.continuousOn_tangentMapWithin (by simp : (1 : ℕ∞ω) ≤ ∞) hU.uniqueMDiffOn
  have hs : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hc := h.comp hs.continuousOn (fun t ht => ht)
  apply hc.congr
  intro t ht
  dsimp only [curveState, tangentMapWithin, Function.comp_def]
  rw [mfderivWithin_of_isOpen hU ht]

def IsIntrinsicGeodesicOn (γ : ℝ → M) (C : ℝ) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ U ∧
  ∀ t ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
    dist (γ s) (γ r) = C * |s - r|

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
 theorem IsIntrinsicGeodesicOn.mono {γ : ℝ → M} {C : ℝ} {U V : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) (hVU : V ⊆ U) :
    IsIntrinsicGeodesicOn (E := E) γ C V :=
  ⟨h.1.mono hVU, fun t ht => h.2 t (hVU ht)⟩

end

 theorem intrinsic_unique_on {γ η : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U)
    (hη : IsIntrinsicGeodesicOn (E := E) η D U)
    {a : ℝ} (ha : a ∈ U) (he : curveState (E := E) γ a = curveState (E := E) η a) :
    EqOn γ η U := by
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  let A : Set U := {t | curveState (E := E) γ t = curveState (E := E) η t}
  have hclosed : IsClosed A := isClosed_eq
    (continuousOn_iff_continuous_domRestrict.mp (curveState_continuousOn hU hγ.1))
    (continuousOn_iff_continuous_domRestrict.mp (curveState_continuousOn hU hη.1))
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hh := intrinsic_germ_unique_on hU hγ.1 hη.1 t.property hC hD
      (hγ.2 t t.property) (hη.2 t t.property) ht
    have hs := hh.eventuallyEq_nhds.mono (fun s hs => curveState_congr (E := E) hs)
    exact continuous_subtype_val.continuousAt hs
  have huniv := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨⟨a, ha⟩, he⟩
  intro t ht
  have h : (⟨t, ht⟩ : U) ∈ A := by rw [huniv]; exact mem_univ _
  exact congrArg TotalSpace.proj h

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI

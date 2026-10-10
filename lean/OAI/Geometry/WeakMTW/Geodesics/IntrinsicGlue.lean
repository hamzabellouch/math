import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicOn

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

def IsIntrinsicGeodesicAt (γ : ℝ → M) (C t : ℝ) : Prop :=
  ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ t ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
    dist (γ s) (γ r) = C * |s - r|

 theorem IsIntrinsicGeodesicOn.at {γ : ℝ → M} {C t : ℝ} {U : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) (hU : IsOpen U) (ht : t ∈ U) :
    IsIntrinsicGeodesicAt (E := E) γ C t :=
  ⟨(h.1 t ht).contMDiffAt (hU.mem_nhds ht), h.2 t ht⟩

 theorem intrinsicOn_of_at {γ : ℝ → M} {C : ℝ} {U : Set ℝ}
    (h : ∀ t ∈ U, IsIntrinsicGeodesicAt (E := E) γ C t) :
    IsIntrinsicGeodesicOn (E := E) γ C U :=
  ⟨fun t ht => (h t ht).1.contMDiffWithinAt, fun t ht => (h t ht).2⟩

 theorem IsIntrinsicGeodesicAt.congr {γ η : ℝ → M} {C t : ℝ}
    (h : IsIntrinsicGeodesicAt (E := E) γ C t) (he : η =ᶠ[𝓝 t] γ) :
    IsIntrinsicGeodesicAt (E := E) η C t := by
  refine ⟨h.1.congr_of_eventuallyEq he, ?_⟩
  obtain ⟨ε, hε, hd⟩ := h.2
  obtain ⟨δ, hδ, hδe⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro s hs r hr
  have hsε := lt_of_lt_of_le hs (min_le_left ε δ)
  have hrε := lt_of_lt_of_le hr (min_le_left ε δ)
  have hsδ := lt_of_lt_of_le hs (min_le_right ε δ)
  have hrδ := lt_of_lt_of_le hr (min_le_right ε δ)
  rw [hδe hsδ, hδe hrδ]
  exact hd s hsε r hrε

 theorem intrinsic_speed_eq_of_germ {γ η : ℝ → M} {C D t : ℝ}
    (hγ : IsIntrinsicGeodesicAt (E := E) γ C t)
    (hη : IsIntrinsicGeodesicAt (E := E) η D t) (he : γ =ᶠ[𝓝 t] η) : C = D := by
  obtain ⟨ε, hε, hc⟩ := hγ.2
  obtain ⟨δ, hδ, hd⟩ := hη.2
  obtain ⟨r, hr, hre⟩ := Metric.eventually_nhds_iff.mp he
  let a := min ε (min δ r) / 2
  have ha : 0 < a := half_pos (lt_min hε (lt_min hδ hr))
  have haε : a < ε := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le (min_le_left _ _)
  have haδ : a < δ := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have har : a < r := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdist : dist (t + a) t = a := by simp [abs_of_pos ha]
  have he₁ := hre (show dist (t + a) t < r by rw [hdist]; exact har)
  have h₁ := hc (t + a) (by change dist (t+a) t < ε; rwa [hdist]) t (Metric.mem_ball_self hε)
  have h₂ := hd (t + a) (by change dist (t+a) t < δ; rwa [hdist]) t (Metric.mem_ball_self hδ)
  rw [he₁, he.eq_of_nhds, h₂] at h₁
  have habs : |t + a - t| = a := by simp [abs_of_pos ha]
  rw [habs] at h₁
  exact (mul_right_cancel₀ ha.ne' h₁).symm

end

 theorem intrinsic_piecewise {γ η : ℝ → M} {C : ℝ} (hC : 0 ≤ C)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V) (hUV : IsPreconnected (U ∩ V))
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U)
    (hη : IsIntrinsicGeodesicOn (E := E) η C V)
    {a : ℝ} (ha : a ∈ U ∩ V) (he : curveState (E := E) γ a = curveState (E := E) η a) :
    IsIntrinsicGeodesicOn (E := E) (U.piecewise γ η) C (U ∪ V) := by
  classical
  have heq := intrinsic_unique_on (hU.inter hV) hUV hC hC
    (hγ.mono inter_subset_left) (hη.mono inter_subset_right) ha he
  apply intrinsicOn_of_at
  intro t ht
  by_cases hu : t ∈ U
  · apply (hγ.at hU hu).congr
    filter_upwards [hU.mem_nhds hu] with s hs
    exact piecewise_eq_of_mem U γ η hs
  · have hv : t ∈ V := ht.resolve_left hu
    apply (hη.at hV hv).congr
    filter_upwards [hV.mem_nhds hv] with s hs
    by_cases hsU : s ∈ U
    · rw [piecewise_eq_of_mem U γ η hsU]
      exact heq ⟨hsU, hs⟩
    · exact piecewise_eq_of_notMem U γ η hsU

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem curveState_comp_sub {γ : ℝ → M} {t a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t - a)) :
    curveState (E := E) (fun s => γ (s-a)) t = curveState (E := E) γ (t-a) := by
  refine TotalSpace.ext ?_ ?_
  · rfl
  apply heq_of_eq
  dsimp only [curveState]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ fun s => s-a) t 1 = _
  have hd : HasDerivAt (fun s : ℝ => s-a) 1 t := (hasDerivAt_id t).sub_const a
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s-a) t :=
    mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ fun s : ℝ => s-a) t =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t-a)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s-a) t) :=
    mfderiv_comp t hγ hs
  rw [hcomp]
  simp only [mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t-a) (fderiv ℝ (fun s : ℝ => s-a) t 1) = _
  rw [fderiv_apply_one_eq_deriv, hd.deriv]

 theorem IsIntrinsicGeodesicOn.comp_sub {γ : ℝ → M} {C a : ℝ} {U : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) :
    IsIntrinsicGeodesicOn (E := E) (fun t => γ (t-a)) C ((fun t => t-a) ⁻¹' U) := by
  refine ⟨h.1.comp (contMDiffOn_iff_contDiffOn.mpr
    (contDiff_id.sub contDiff_const).contDiffOn) (fun t ht => ht), ?_⟩
  intro t ht
  obtain ⟨ε, hε, hd⟩ := h.2 (t-a) ht
  refine ⟨ε, hε, ?_⟩
  intro s hs r hr
  have hse : s-a ∈ Metric.ball (t-a) ε := by simpa only [Metric.mem_ball, dist_sub_right] using hs
  have hre : r-a ∈ Metric.ball (t-a) ε := by simpa only [Metric.mem_ball, dist_sub_right] using hr
  simpa only [sub_sub_sub_cancel_right] using hd (s-a) hse (r-a) hre

end
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI

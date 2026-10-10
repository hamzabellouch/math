import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MetricCurveLocal

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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma velocity_lift_eq_of_eventuallyEq {γ δ : ℝ → M} {t : ℝ}
    (he : γ =ᶠ[𝓝 t] δ) :
    (⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M) =
      ⟨δ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t (1:ℝ)⟩ := by
  refine TotalSpace.ext he.self_of_nhds ?_
  exact heq_of_eq (DFunLike.congr_fun he.mfderiv_eq (1 : ℝ))

lemma metric_curve_velocity_isMIntegralCurve {γ : ℝ → M} {k : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ,
      |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    IsMIntegralCurve
      (fun t => (⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M))
      (geodesicSpray (E := E)) := by
  intro t
  obtain ⟨ε,hε,hd⟩ := hloc t
  let δ : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s =>
    sprayFlow (s-t) ⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩
  have hδ : IsMIntegralCurve δ (geodesicSpray (E := E)) :=
    isMIntegralCurve_comp_sub.mpr (sprayFlow_curve _)
  have he : γ =ᶠ[𝓝 t] (fun s => (δ s).1) := metric_curve_eq_spray_local hγ hε hd
  have hL : (fun s => (⟨γ s,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ s (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M))
      =ᶠ[𝓝 t] δ := by
    filter_upwards [he.eventuallyEq_nhds] with s hs
    rw [velocity_lift_eq_of_eventuallyEq hs,
      spray_velocity_eq_mfderiv (hδ.isMIntegralCurveAt s)]
  have H := (hδ t).congr_of_eventuallyEq hL
  rw [←hL.self_of_nhds] at H
  exact H

lemma metric_curve_eq_spray {γ : ℝ → M} {k : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ,
      |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    γ = (fun t => (sprayFlow t ⟨γ 0,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ 0 (1:ℝ)⟩).1) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have H := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (contMDiff_geodesicSpray.of_le (by simp))
    (metric_curve_velocity_isMIntegralCurve hγ hloc) (sprayFlow_curve _)
    (sprayFlow_zero _).symm
  funext t
  exact congrArg (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) (congrFun H t)

end

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma geodesicWithInitialData_eq_spray {x : M} {v : TangentSpace 𝓘(ℝ,Model n) x}
    {γ : ℝ → M} (hγ : IsGeodesicWithInitialData x v γ) :
    γ = (fun t => (sprayFlow t ⟨x,v⟩).1) := by
  have H := metric_curve_eq_spray hγ.1 hγ.2.2
  rwa [hγ.2.1] at H

lemma riemannianExp_eq_sprayFlow (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    riemannianExp x v = (sprayFlow 1 ⟨x,v⟩).1 := by
  rw [riemannianExp_eq_chosen_geodesic,
    geodesicWithInitialData_eq_spray (Classical.choose_spec (exists_geodesicWithInitialData x v))]

lemma riemannianExp_smul (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) (t : ℝ) :
    riemannianExp x (t • v) = (sprayFlow t ⟨x,v⟩).1 := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale t ⟨x,v⟩)).1 = _
  rw [sprayFlow_scale,mul_one]
  rfl

lemma contMDiff_riemannianExp :
    ContMDiff (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n) ∞
      (fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 z.2) := by
  have hF : ContMDiff (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun z : TangentBundle 𝓘(ℝ,Model n) M => sprayFlow 1 z) :=
    contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)
  have H := (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).comp hF
  apply H.congr
  intro z
  cases z
  exact riemannianExp_eq_sprayFlow _ _

end WeakMTWTransport

end

end OAI

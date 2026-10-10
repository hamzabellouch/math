import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SplitAction

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

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def diagonalSplitAction (x : M) (t : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  splitNormalAction x t q.1 (0,q.2)

lemma split_regular_legs_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have hscale : Continuous (fun v : TangentSpace 𝓘(ℝ,Model n) x => t • v) := by fun_prop
  have h₁ : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    hscale.continuousAt.preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  have hZ := contMDiff_tangentScale.comp ((contMDiff_const (c := 1-t)).prodMk (contMDiff_spray_fiber (E := Model n) x t))
  have h₂ : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p,
      (1-t) • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 :=
    (hZ.continuous.continuousAt (x := p)).preimage_mem_nhds
      (isOpen_total_injectivityDomain.mem_nhds hright)
  exact h₁.and h₂

lemma diagonalSplitAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (diagonalSplitAction x t) (p,p) :=
  (splitNormalAction_contDiffAt hleft hright).comp (p,p)
    (contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_snd))

lemma diagonalSplitAction_stationary {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (diagonalSplitAction x t) (p,p) (0,xi)=0 := by
  have hD := cost_start_gradient_of_injectivityDomain hright
  rw [shifted_exp_endpoint] at hD
  have hD' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun b => dist b (riemannianExp x p)^2/2)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ ((-(1-t)) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) := by
    simpa only [cost,neg_smul] using hD
  have H := spray_action_line_stationary x p xi t (1-t) (sub_pos.mpr ht1).ne' (riemannianExp x p) hD'
  have hline : ContinuousAt (fun s : ℝ => p+s • xi) 0 := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, t • (p+s • xi) ∈ injectivityDomain x := by
    have hn := (split_regular_legs_near hleft hright).mono (fun _ h => h.1)
    have hl : Tendsto (fun s : ℝ => p+s • xi) (𝓝 0) (𝓝 p) := by simpa only [ContinuousAt,zero_smul,add_zero] using hline
    exact hl.eventually hn
  have heq : (fun s : ℝ => diagonalSplitAction x t (p,p+s • xi)) =ᶠ[𝓝 0]
      (fun s : ℝ => t*‖p+s • xi‖^2/2 +
        dist (sprayFlow t (⟨x,p+s • xi⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 (riemannianExp x p)^2/2/(1-t)) := by
    filter_upwards [hnear] with s hs
    have hm := injectivityDomain_subset_minimizingVectors x hs
    change dist x (riemannianExp x (t • (p+s • xi)))=‖t • (p+s • xi)‖ at hm
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,cost]
    rw [hm,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    rw [riemannianExp_smul]
    field_simp
  have hstat := H.congr_of_eventuallyEq heq
  have hp₀ : HasDerivAt (fun s : ℝ => (p,p+s • xi)) (0,xi) 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).prodMk
      ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)) using 1
    simp
  have hf := ((diagonalSplitAction_contDiffAt hleft hright).differentiableAt (by simp)).hasFDerivAt
  have hf' : HasFDerivAt (diagonalSplitAction x t)
      (fderiv ℝ (diagonalSplitAction x t) (p,p)) (p,p+(0:ℝ) • xi) := by
    simpa only [zero_smul,add_zero] using hf
  exact (hf'.comp_hasDerivAt (f := fun s : ℝ => (p,p+s • xi)) 0 hp₀).unique hstat

end WeakMTWTransport

end

end OAI

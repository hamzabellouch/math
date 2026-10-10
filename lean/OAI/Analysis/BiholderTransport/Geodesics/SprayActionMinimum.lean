import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingSubinterval
import OAI.Analysis.BiholderTransport.Geodesics.ShortGradient
import OAI.Analysis.BiholderTransport.Regularity.ActionKernel

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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma spray_split_action_contact (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {L ε : ℝ} (hL : 0<L) (hε : 0<ε)
    (hmin : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖) :
    L*‖p‖^2/2 +
      dist (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 (sprayFlow (L+ε) ⟨x,p⟩).1^2/(2*ε) +
      dist (sprayFlow (L+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 (sprayFlow (L+2*ε) ⟨x,p⟩).1^2/(2*ε) =
      (L+2*ε)*‖p‖^2/2 := by
  have hpre := sprayFlow_minimizing_prefix (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L+ε) (by positivity) (by linarith) hmin
  have h₁ := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L) hL.le (by linarith : L≤L+ε) hpre
  have h₂ := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L+ε) (by positivity) (by linarith : L+ε≤L+2*ε) hmin
  rw [h₁,h₂]
  dsimp
  field_simp
  ring

lemma spray_split_action_minimum (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {L ε : ℝ} (hL : 0<L) (hε : 0<ε)
    (hmin : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖)
    (v : TangentSpace 𝓘(ℝ,E) x) (q : M) :
    (L+2*ε)*‖p‖^2/2 ≤ L*‖v‖^2/2 +
      dist (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q^2/(2*ε) +
      dist q (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1^2/(2*ε) := by
  have hb : dist x (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ≤ L*‖v‖ := by
    simpa only [sprayFlow_zero,zero_sub,abs_neg,abs_of_pos hL] using
      dist_sprayFlow_le (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) 0 L
  have hh := three_leg_energy_le x (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q
    (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 hL hε hb
  rw [hmin] at hh
  have he : ((L+2*ε)*‖p‖)^2/(2*(L+2*ε)) = (L+2*ε)*‖p‖^2/2 := by
    have hn : L+2*ε ≠ 0 := (show 0<L+2*ε by positivity).ne'
    field_simp
  rwa [he] at hh

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_spray_fiber_immersion (x : M) (p : TangentSpace 𝓘(ℝ,E) x) (t : ℝ) :
    Function.Injective (fderiv ℝ
      (fun v : TangentSpace 𝓘(ℝ,E) x =>
        extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t ⟨x,p⟩) (sprayFlow t ⟨x,v⟩)) p) := by
  let z : TangentBundle 𝓘(ℝ,E) M := ⟨x,p⟩
  let a := sprayFlow t z
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let χ₀ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z
  let Φ : TangentSpace 𝓘(ℝ,E) x → E×E := fun v => χ (sprayFlow t ⟨x,v⟩)
  let K : E×E → E×E := fun y => χ₀ (sprayFlow (-t) (χ.symm y))
  let R : E×E → E := fun y => (K y).2
  have hΦp : Φ p = χ a := rfl
  have hχinv : χ.symm (Φ p) = a := χ.left_inv (mem_extChartAt_source a)
  have hback : sprayFlow (-t) (χ.symm (Φ p)) = z := by
    rw [hχinv]
    exact (sprayFlow_add (-t) t z).symm.trans (by rw [neg_add_cancel,sprayFlow_zero])
  have hΦ : ContDiffAt ℝ ∞ Φ p :=
    ((show ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ a from
      contMDiffAt_extChartAt).comp p (contMDiff_spray_fiber x t p)).contDiffAt
  have hχ : ContMDiffAt 𝓘(ℝ,E×E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ χ.symm (Φ p) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (χ.map_source (mem_extChartAt_source a)))
  have hf : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (sprayFlow (-t) : TangentBundle 𝓘(ℝ,E) M → TangentBundle 𝓘(ℝ,E) M) :=
    contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)
  have hχ₀ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ₀
      (sprayFlow (-t) (χ.symm (Φ p))) := by
    rw [hback]; exact contMDiffAt_extChartAt
  have hK : ContDiffAt ℝ ∞ K (Φ p) :=
    (hχ₀.comp (Φ p) ((hf (χ.symm (Φ p))).comp (Φ p) hχ)).contDiffAt
  have hR : DifferentiableAt ℝ R (Φ p) := hK.snd.differentiableAt (by simp)
  let e := trivializationAt E (fun b : M => TangentSpace 𝓘(ℝ,E) b) x
  let L : TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] E :=
    e.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt E _ x)
  have hnear : ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p, sprayFlow t ⟨x,v⟩ ∈ χ.source :=
    (contMDiff_spray_fiber x t p).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a))
  have heq : (fun v => R (Φ v)) =ᶠ[𝓝 p] L := by
    filter_upwards [hnear] with v hv
    dsimp [R,K,Φ]
    rw [χ.left_inv hv,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    rfl
  have hd := (hR.hasFDerivAt.comp p (hΦ.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun v => R (Φ v)) p = _ at hd
  rw [heq.fderiv_eq,L.hasFDerivAt.fderiv] at hd
  intro u v huv
  change fderiv ℝ Φ p u = fderiv ℝ Φ p v at huv
  apply L.injective
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E => A u-A v) hd
  simp only [ContinuousLinearMap.comp_apply,huv,sub_self,sub_eq_zero] at hh
  convert! hh

end WeakMTWTransport

end

end OAI

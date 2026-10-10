import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayNonconjugacy

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma riemannianExp_interior_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p) := by
  obtain ⟨a,ha,hpa⟩ := hp
  have hm : dist x (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 = a*‖p‖ := by
    rw [←riemannianExp_smul]
    exact hpa
  simpa only [riemannianExp_eq_sprayFlow] using
    sprayFlow_interior_nonconjugate x p zero_lt_one ha hm

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contMDiff_riemannianExp_fiber (x : M) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞ (riemannianExp (n := n) x) := by
  have H := (Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,Model n) z)).comp
    (contMDiff_spray_fiber x 1)
  apply H.congr
  intro v
  exact riemannianExp_eq_sprayFlow x v

lemma exists_coordinate_exp_inverse {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    ∃ e : OpenPartialHomeomorph (TangentSpace 𝓘(ℝ,Model n) x) (Model n),
      (e : TangentSpace 𝓘(ℝ,Model n) x → Model n) =
        (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)) ∧
      p ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (e p) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let f := fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)
  have hf : ContDiffAt ℝ ∞ f p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) (riemannianExp (n := n) x p) from
      contMDiffAt_extChartAt).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  let D := fderiv ℝ f p
  have hi : Function.Injective D := riemannianExp_interior_nonconjugate hp
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) x
  let L : TangentSpace 𝓘(ℝ,Model n) x ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt (Model n) _ x)
  have hs : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank L.toLinearEquiv.finrank_eq).mp hi
  let A := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs)
  have hd : HasFDerivAt f (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) p :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  have he : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,he,?_⟩
  apply e.contDiffAt_symm (e.map_source he)
  · rw [e.left_inv he]
    convert! hd using 1
  · rw [e.left_inv he]
    exact hf

lemma riemannianExp_locally_injective {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    ∃ U, IsOpen U ∧ p ∈ U ∧ Set.InjOn (riemannianExp (n := n) x) U := by
  obtain ⟨e,he,hp',_⟩ := exists_coordinate_exp_inverse hp
  refine ⟨e.source,e.open_source,hp',?_⟩
  intro v hv w hw h
  apply e.injOn hv hw
  rw [he]
  exact congrArg (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) h

end WeakMTWTransport

end

end OAI

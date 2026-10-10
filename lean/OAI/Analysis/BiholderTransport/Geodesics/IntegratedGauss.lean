import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.GlobalGauss

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma spray_variation_pairing_affine
    {ν : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hν : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ ν)
    {s e : ℝ} (he : HasDerivAt (fun r => ‖(ν r).2‖^2) e s) (t : ℝ) :
    inner ℝ (sprayFlow t (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow t (ν k)).1) s 1) =
    inner ℝ (ν s).2 (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (ν k).1) s 1) + t*(e/2) := by
  let P : ℝ → ℝ := fun r => inner ℝ (sprayFlow r (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow r (ν k)).1) s 1)
  have hP (r : ℝ) : HasDerivAt P (e/2) r := spray_variation_pairing_hasDerivAt hν he r
  have hd (r : ℝ) : HasDerivAt (fun q => P q-q*(e/2)) 0 r := by
    convert! (hP r).sub ((hasDerivAt_id r).mul_const (e/2)) using 1; simp
  have hc := is_const_of_deriv_eq_zero
    (fun point => (hd point).differentiableAt)
    (fun point => (hd point).deriv) t (0 : ℝ)
  have hP0 : P 0 = inner ℝ (ν s).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (ν k).1) s 1) := by
    have hflow0 : (fun k => sprayFlow 0 (ν k)) = ν := funext (fun k => sprayFlow_zero (ν k))
    exact congrArg (fun γ : ℝ → TangentBundle 𝓘(ℝ,E) M =>
      inner ℝ (γ s).2 (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (γ k).1) s 1)) hflow0
  simp only [zero_mul,sub_zero,hP0] at hc
  dsimp [P] at hc
  linarith

lemma sprayFlow_gauss (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) (t : ℝ) :
    inner ℝ (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun s : ℝ => (sprayFlow t (⟨x,v+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)).1) 0 1) =
    t*inner ℝ v w := by
  let ν : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s => ⟨x,v+s • w⟩
  have he : HasDerivAt (fun s : ℝ => ‖(ν s).2‖^2) (2*inner ℝ v w) 0 := by
    have hh := ((hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq
    simpa [ν] using hh
  have hh := spray_variation_pairing_affine (ν := ν) (contMDiff_fiber_line x v w) he t
  have hν0 : ν 0 = (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) := by
    dsimp [ν]; rw [zero_smul,add_zero]
  rw [hν0] at hh
  convert! hh using 1
  simp [ν]

end WeakMTWTransport

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.NoCorner
import OAI.Analysis.BiholderTransport.Geodesics.IntegratedGauss

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

lemma exists_local_spray_cost_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, ∀ t : ℝ, 0 < t →
      z.1 ∈ Metric.ball a δ → (sprayFlow t z).1 ∈ Metric.ball a δ →
      dist z.1 (sprayFlow t z).1 = t*‖z.2‖ →
      HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist z.1 y^2/2)
        (sprayFlow t z).1 (innerSL ℝ (t • (sprayFlow t z).2)) := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z t ht hz hy hmin
  obtain ⟨⟨b,w⟩,hb,hn,_,hD⟩ := H z.1 hz (sprayFlow t z).1 hy
  dsimp only at hb
  subst b
  have hw := sprayFlow_minimizer_gradient z ht hmin w hn hD
  rwa [hw] at hD

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma sprayFlow_reverse (z : TangentBundle 𝓘(ℝ,E) M) (t : ℝ) :
    sprayFlow t (tangentScale (-1) (sprayFlow t z)) = tangentScale (-1) z := by
  rw [sprayFlow_scale,neg_one_mul,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

lemma exists_local_spray_cost_start_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, ∀ t : ℝ, 0 < t →
      z.1 ∈ Metric.ball a δ → (sprayFlow t z).1 ∈ Metric.ball a δ →
      dist z.1 (sprayFlow t z).1 = t*‖z.2‖ →
      HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist y (sprayFlow t z).1^2/2)
        z.1 (innerSL ℝ ((-t) • z.2)) := by
  obtain ⟨δ,hδ,H⟩ := exists_local_spray_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z t ht hz hy hmin
  let w := tangentScale (-1) (sprayFlow t z)
  have hw : sprayFlow t w = tangentScale (-1) z := sprayFlow_reverse z t
  have hb : (sprayFlow t w).1 ∈ Metric.ball a δ := by rw [hw]; exact hz
  have hm : dist w.1 (sprayFlow t w).1 = t*‖w.2‖ := by
    rw [hw]
    change dist (sprayFlow t z).1 z.1 = t*‖(-1:ℝ) • (sprayFlow t z).2‖
    rw [neg_one_smul,norm_neg,sprayFlow_speed,dist_comm,hmin]
  have hd := H w t ht hy hb hm
  rw [hw] at hd
  change HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist (sprayFlow t z).1 y^2/2)
    z.1 (innerSL ℝ (t • ((-1:ℝ) • z.2))) at hd
  rw [smul_smul,mul_neg_one] at hd
  have hf : (fun y => dist y (sprayFlow t z).1^2/2) =
      (fun y => dist (sprayFlow t z).1 y^2/2) := by
    funext y; rw [dist_comm]
  rw [hf]
  exact hd

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_fiber_embedding (x : M) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun v : TangentSpace 𝓘(ℝ,E) x => (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const,?_⟩
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ,E) y) x
  let L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E := e.continuousLinearMapAt ℝ x
  have heq : (fun w : TangentSpace 𝓘(ℝ,E) x => (e (⟨x,w⟩ : TangentBundle 𝓘(ℝ,E) M)).2) = L := by
    funext w
    exact (e.continuousLinearMapAt_apply_of_mem ℝ (mem_baseSet_trivializationAt E _ x) _).symm
  change ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) 𝓘(ℝ,E) ∞
    (fun w => (e ⟨x,w⟩).2) v
  rw [heq]
  exact L.contDiff.contDiffAt.contMDiffAt

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_spray_fiber (x : M) (t : ℝ) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun v : TangentSpace 𝓘(ℝ,E) x => sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
  contMDiff_sprayFlow.comp (contMDiff_const.prodMk (contMDiff_fiber_embedding x))

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma spray_action_line_stationary (x : M) (p w : TangentSpace 𝓘(ℝ,E) x)
    (L ε : ℝ) (hε : ε ≠ 0) (y : M)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => dist b y^2/2)
      (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
      (innerSL ℝ ((-ε) • (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).2))) :
    HasDerivAt (fun s : ℝ => L*‖p+s • w‖^2/2 +
      (dist (sprayFlow L (⟨x,p+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)).1 y^2/2)/ε) 0 0 := by
  let ν : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s => sprayFlow L ⟨x,p+s • w⟩
  let ψ : ℝ → M := fun s => (ν s).1
  have hψ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ ψ :=
    (Bundle.contMDiff_proj (fun b : M => TangentSpace 𝓘(ℝ,E) b)).comp
      (contMDiff_sprayFlow.comp (contMDiff_const.prodMk (contMDiff_fiber_line x p w)))
  have hν0 : ν 0 = sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M) := by simp [ν]
  have hD₀ : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => dist b y^2/2) (ν 0).1
      (innerSL ℝ ((-ε) • (ν 0).2)) := by rw [hν0]; exact hD
  have hDc := hD₀.comp 0 (hψ.mdifferentiable (by simp) 0).hasMFDerivAt
  let J := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ψ 0 (1:ℝ)
  have hd : HasDerivAt (fun s => dist (ψ s) y^2/2)
      ((-ε) * inner ℝ (ν 0).2 J) 0 := by
    have hf : HasFDerivAt (fun s => dist (ψ s) y^2/2)
        ((innerSL ℝ ((-ε) • (ν 0).2)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ψ 0)) 0 := by
      convert! hDc.hasFDerivAt using 1
    convert! hf.hasDerivAt using 1
    change (-ε) * inner ℝ (ν 0).2 J = inner ℝ ((-ε) • (ν 0).2) J
    rw [real_inner_smul_left]
  have hg : inner ℝ (ν 0).2 J = L*inner ℝ p w := by
    have he : HasDerivAt (fun s : ℝ => ‖p+s • w‖^2) (2*inner ℝ p w) 0 := by
      convert! ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq using 1
      simp
    have H := spray_variation_pairing_affine (ν := fun s => (⟨x,p+s • w⟩ : TangentBundle 𝓘(ℝ,E) M))
      (contMDiff_fiber_line x p w) he L
    convert! H using 1
    simp
  have hn := ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq
  have he : HasDerivAt (fun s : ℝ => L*‖p+s • w‖^2/2) (L*inner ℝ p w) 0 := by
    convert! (hn.const_mul L).div_const 2 using 1
    simp
    ring
  have H := he.add (hd.div_const ε)
  apply H.congr_deriv
  rw [hg]
  field_simp
  ring

end WeakMTWTransport

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SplitMinimizingAction
import OAI.Analysis.BiholderTransport.CostGeometry.CostSmooth
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldMinimum

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_start_gradient_of_injectivityDomain {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun y => cost y (riemannianExp x p))
      x (innerSL ℝ (-p)) := by
  have hpmin := injectivityDomain_subset_minimizingVectors x hp
  obtain ⟨δ,hδ,H⟩ := exists_local_spray_cost_start_gradient (E := Model n) x
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, riemannianExp x (s • p) ∈ Metric.ball x δ := by
    have ht : ContinuousAt (fun s : ℝ => riemannianExp x (s • p)) 0 :=
      ((continuous_riemannianExp x).comp (continuous_id.smul continuous_const)).continuousAt
    have hx : riemannianExp x ((0:ℝ) • p) ∈ Metric.ball x δ := by simpa using hδ
    exact ht.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0,
      riemannianExp x (s • p) ∈ Metric.ball x δ ∧ s<1 ∧ 0<s :=
    (hnear.filter_mono nhdsWithin_le_nhds).and
      (((show ∀ᶠ r : ℝ in 𝓝 0, r<1 from eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨s,hy,hs1,hs⟩ := hsmall.exists
  have hz : x ∈ Metric.ball x δ := by simpa using hδ
  have hys : (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 ∈ Metric.ball x δ := by
    rwa [←riemannianExp_smul]
  have hmin : dist x (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=s*‖p‖ := by
    rw [←riemannianExp_smul,minimizingVectors_smul hpmin hs.le hs1.le,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  have hD := H ⟨x,p⟩ s hs hz hys hmin
  rw [←riemannianExp_smul] at hD
  dsimp only at hD
  let G : M → ℝ := fun y => cost y (riemannianExp x (s • p))/s+(1-s)*‖p‖^2/2
  have hG : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) G x (innerSL ℝ (-p)) := by
    have HH := (hD.const_smul (s⁻¹)).add
      (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ)) ((1-s)*‖p‖^2/2) x)
    have hGG : G =ᶠ[𝓝 x]
        ((s⁻¹ • fun y => dist y (riemannianExp x (s • p))^2/2) + fun _ => (1-s)*‖p‖^2/2) := by
      apply Filter.Eventually.of_forall
      intro y
      dsimp [G,cost]
      simp only [div_eq_mul_inv]
      ring
    apply (HH.congr_of_eventuallyEq hGG).congr_mfderiv
    have heq : (s⁻¹ • innerSL ℝ ((-s) • p)) + 0 = innerSL ℝ (-p) := by
      ext v
      simp only [_root_.smul_apply,add_zero,innerSL_apply_apply,real_inner_smul_left,inner_neg_left,smul_eq_mul]
      field_simp [ne_of_gt hs]
    convert! heq using 1
  have hcost := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hF : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun y => cost y (riemannianExp x p)) x :=
    ((hcost.comp x (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp))
  have heq := upper_contact_mfderiv hF hG.mdifferentiableAt
    (Filter.Eventually.of_forall (minimizing_split_upper_support hpmin hs hs1))
    (minimizing_split_contact hpmin hs hs1).symm
  exact hF.hasMFDerivAt.congr_mfderiv (heq.trans hG.mfderiv)

end WeakMTWTransport

end

end OAI

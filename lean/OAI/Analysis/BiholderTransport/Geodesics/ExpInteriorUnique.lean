import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayMinimizerUnique

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
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma riemannianExp_interior_unique {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (hq : q ∈ minimizingVectors x)
    (he : riemannianExp x p = riemannianExp x q) : p=q := by
  have hpmin := injectivityDomain_subset_minimizingVectors x hp
  have hn : ‖p‖=‖q‖ := hpmin.symm.trans ((congrArg (dist x) he).trans hq)
  by_cases hp0 : p=0
  · have hq0 : q=0 := norm_eq_zero.mp (by rw [←hn,hp0,norm_zero])
    exact hp0.trans hq0.symm
  have ht : 0<‖p‖ := norm_pos_iff.mpr hp0
  obtain ⟨a,ha,hpa⟩ := hp
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,‖p‖⁻¹ • p⟩
  let w : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,‖p‖⁻¹ • q⟩
  have hzn : ‖z.2‖=1 := by
    change ‖‖p‖⁻¹ • p‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),inv_mul_cancel₀ ht.ne']
  have hwn : ‖w.2‖=1 := by
    change ‖‖p‖⁻¹ • q‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),←hn,inv_mul_cancel₀ ht.ne']
  have hflowz : (sprayFlow ‖p‖ z).1=riemannianExp x p := by
    rw [←riemannianExp_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hfloww : (sprayFlow ‖p‖ w).1=riemannianExp x q := by
    rw [←riemannianExp_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hflowa : (sprayFlow (a*‖p‖) z).1=riemannianExp x (a • p) := by
    rw [←riemannianExp_smul,smul_smul,mul_assoc,mul_inv_cancel₀ ht.ne',mul_one]
  have hzw := sprayFlow_unit_minimizer_unique z w rfl hzn hwn ht
    (lt_mul_of_one_lt_left ht ha)
    (by rw [hflowa]; exact hpa)
    (by rw [hfloww,hn]; exact hq)
    (by rw [hflowz,hfloww]; exact he)
  have hvel : ‖p‖⁻¹ • p = ‖p‖⁻¹ • q := TotalSpace.mk_injective x hzw
  exact (smul_right_inj (inv_ne_zero ht.ne')).mp hvel

lemma riemannianExp_injOn_injectivityDomain (x : M) :
    Set.InjOn (riemannianExp (n := n) x) (injectivityDomain x) := by
  intro p hp q hq he
  exact riemannianExp_interior_unique hp (injectivityDomain_subset_minimizingVectors x hq) he

end WeakMTWTransport

end

end OAI

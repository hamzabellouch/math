import Mathlib
import OAI.Analysis.SymmetricDomains.HolQuadraticSmul
import OAI.Analysis.SymmetricDomains.QuadraticDomainConnectedComponent

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

lemma hermQuadratic_continuous (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    Continuous (hermQuadratic B) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  apply continuous_pi
  intro i
  let b : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (B i))
  have hq : Continuous (fun z : E => B i z z) :=
    b.continuous.clm_apply continuous_id
  have hqI : Continuous (fun z : E => B i (I • z) (I • z)) :=
    hq.comp (continuous_const.smul continuous_id)
  have he : (fun z => hermQuadratic B z i) =
      (fun z => (B i z z+B i (I • z) (I • z))/2) := by
    funext z
    simp [hermQuadratic,hermPart,symmetrize_diag]
  rw [he]
  exact (hq.add hqI).div_const 2

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma hermQuadratic_zero (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    hermQuadratic B 0 = 0 := by
  funext i
  simp [hermQuadratic,hermPart_zero]

omit [FiniteDimensional ℂ E] in

theorem actual_quadratic_model_invariances
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hcone : ∀ r : ℝ, 0 < r → ∀ v, r • v ∈ C ↔ v ∈ C) :
    (∀ (p : E × (Fin k → ℂ)) (a : Fin k → ℝ), (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) ∧
    (∀ c : ℂ, ‖c‖ = 1 → ∀ p,
      (c • p.1,p.2) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) ∧
    (∀ r : ℝ, 0 < r → ∀ p,
      (Real.sqrt r • p.1,r • p.2) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) := by
  refine ⟨fun p a => quadraticDomain_translation _ _ p a,?_,?_⟩
  · intro c hc p
    exact quadraticDomain_unit_rotation _ _ c (hermQuadratic_unit B c hc) p
  · intro r hr p
    apply quadraticDomain_positive_dilation _ _ r _ (hcone r hr) p
    intro z
    rw [hermQuadratic_real_smul,Real.sq_sqrt hr.le]

theorem actual_quadratic_model_domain
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hC : IsOpen C) (hc : IsConnected C) :
    IsOpen (quadraticDomain (hermQuadratic B) C) ∧
    IsConnected (quadraticDomain (hermQuadratic B) C) ∧
    ∃ a : Fin k → ℝ, ((0 : E),fun i => I*(a i : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
  refine ⟨quadraticDomain_isOpen _ (hermQuadratic_continuous B) C hC,
    quadraticDomain_isConnected _ (hermQuadratic_continuous B) C hc,?_⟩
  obtain ⟨a,ha⟩ := hc.nonempty
  exact ⟨a,quadraticDomain_axis _ (hermQuadratic_zero B) ha⟩

end Release061.Hermitian

end

end OAI

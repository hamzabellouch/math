import Mathlib
import OAI.Analysis.SymmetricDomains.HeisenbergShiftAxis

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

def normalTranslation (a : Fin k → ℝ) : (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) :=
  Homeomorph.addRight (0,fun i => (a i : ℂ))

omit [IsScalarTower ℝ ℂ E] [NormedSpace ℝ E] [FiniteDimensional ℂ E] in
lemma normalTranslation_analytic (a : Fin k → ℝ) :
    AnalyticOnNhd ℂ (normalTranslation (E := E) a) univ := by
  intro p _
  exact analyticAt_id.add analyticAt_const

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma normalTranslation_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (a : Fin k → ℝ) (p : E × (Fin k → ℂ)) :
    normalTranslation a p ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C := by
  change (fun i => (p.2 i+(a i : ℂ)).im-hermQuadratic B (p.1+0) i) ∈ C ↔ _
  simp only [add_zero,add_im,ofReal_im,add_zero]
  rfl

def axisNormalization (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (p : E × (Fin k → ℂ)) : (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) :=
  (heisenbergHomeomorph B (-p.1)).trans
    (normalTranslation (fun i => -(p.2 i).re))

lemma axisNormalization_apply
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    axisNormalization B p p =
      (0,fun i => I*((p.2 i).im-hermQuadratic B p.1 i : ℝ)) := by
  change normalTranslation _ (heisenbergShift B (-p.1) p) = _
  rw [heisenbergShift_axis]
  apply Prod.ext
  · simp [normalTranslation]
  · funext i
    apply Complex.ext <;> simp [normalTranslation]

lemma axisNormalization_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (p q : E × (Fin k → ℂ)) :
    axisNormalization B p q ∈ quadraticDomain (hermQuadratic B) C ↔
      q ∈ quadraticDomain (hermQuadratic B) C := by
  change normalTranslation _ (heisenbergShift B (-p.1) q) ∈ _ ↔ _
  rw [normalTranslation_mem,heisenbergShift_mem]

lemma axisNormalization_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    AnalyticOnNhd ℂ (axisNormalization B p) univ := by
  intro q _
  exact (normalTranslation_analytic _ _ (mem_univ _)).comp
    (heisenbergShift_analytic B (-p.1) q (mem_univ _))

def axisNormalizationModel (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (C : Set (Fin k → ℝ)) (p : E × (Fin k → ℂ)) :
    quadraticDomain (hermQuadratic B) C ≃ₜ quadraticDomain (hermQuadratic B) C :=
  (axisNormalization B p).subtype (fun q => (axisNormalization_mem B C p q).symm)

lemma axisNormalization_inverse_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    AnalyticOnNhd ℂ (axisNormalization B p).symm univ := by
  intro q _
  have ht : AnalyticAt ℂ (normalTranslation (E := E) (fun i => -(p.2 i).re)).symm q := by
    unfold normalTranslation
    rw [Homeomorph.addRight_symm]
    exact analyticAt_id.add analyticAt_const
  exact (heisenbergShift_analytic B (-(-p.1)) _ (mem_univ _)).comp ht

theorem quadratic_model_residual_fiber_transitive
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (p q : E × (Fin k → ℂ))
    (hpq : (fun i => (p.2 i).im-hermQuadratic B p.1 i) =
      (fun i => (q.2 i).im-hermQuadratic B q.1 i)) :
    ∃ e : (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)),
      AnalyticOnNhd ℂ e univ ∧ AnalyticOnNhd ℂ e.symm univ ∧
      (∀ x, e x ∈ quadraticDomain (hermQuadratic B) C ↔
        x ∈ quadraticDomain (hermQuadratic B) C) ∧ e p = q := by
  let ep := axisNormalization B p
  let eq := axisNormalization B q
  have heq : ep p = eq q := by
    change axisNormalization B p p = axisNormalization B q q
    rw [axisNormalization_apply,axisNormalization_apply]
    apply Prod.ext
    · rfl
    · funext i
      exact congrArg (fun v : Fin k → ℝ => I*(v i : ℂ)) hpq
  refine ⟨ep.trans eq.symm,?_,?_,?_,?_⟩
  · intro x _
    exact (axisNormalization_inverse_analytic B q _ (mem_univ _)).comp
      (axisNormalization_analytic B p x (mem_univ _))
  · intro x _
    exact (axisNormalization_inverse_analytic B p _ (mem_univ _)).comp
      (axisNormalization_analytic B q x (mem_univ _))
  · intro x
    change eq.symm (ep x) ∈ _ ↔ x ∈ _
    have hs := axisNormalization_mem B C q (eq.symm (ep x))
    change eq (eq.symm (ep x)) ∈ _ ↔ eq.symm (ep x) ∈ _ at hs
    rw [eq.apply_symm_apply] at hs
    exact hs.symm.trans (axisNormalization_mem B C p x)
  · change eq.symm (ep p) = q
    rw [heq,eq.symm_apply_apply]

end Release061.Hermitian

end

end OAI

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Smoothness in a finite-dimensional space of functions

Point evaluations span the dual of a finite-dimensional function space.
Consequently scalar pointwise smoothness detects smoothness into that space.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {G V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  (e : V →ₗ[ℝ] (G → ℝ))

def coordinateEvaluation (g : G) : Module.Dual ℝ V where
  toFun v := e v g
  map_add' v w := by simp
  map_smul' a v := by simp

theorem span_coordinateEvaluation (he : Function.Injective e) :
    Submodule.span ℝ (Set.range (coordinateEvaluation e)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (coordinateEvaluation e))
  have hS : S.dualCoannihilator = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    apply he
    ext g
    have h := ((Submodule.mem_dualCoannihilator v).mp hv) (coordinateEvaluation e g)
      (Submodule.subset_span (Set.mem_range_self g))
    simpa only [coordinateEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_zero,
      Pi.zero_apply] using h
  calc
    S = S.dualCoannihilator.dualAnnihilator :=
      Subspace.dualCoannihilator_dualAnnihilator_eq.symm
    _ = ⊤ := by rw [hS, Submodule.dualAnnihilator_bot]

theorem contDiff_of_coordinateEvaluations (he : Function.Injective e)
    {r : ℕ∞ω} {F : X → V} (hF : ∀ g, ContDiff ℝ r (fun x => e (F x) g)) :
    ContDiff ℝ r F := by
  have hlin (f : Module.Dual ℝ V) : ContDiff ℝ r (fun x => f (F x)) := by
    have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
      rw [span_coordinateEvaluation e he]
      trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, rfl⟩ := hf
      exact hF g
    | zero => exact contDiff_const
    | add f g _ _ hf hg => exact hf.add hg
    | smul a f _ hf => exact hf.const_smul a
  let b := Module.finBasis ℝ V
  let E := b.equivFun.toContinuousLinearEquiv
  have hc : ContDiff ℝ r (fun x => E (F x)) := by
    apply contDiff_pi.mpr
    intro i
    exact hlin ((LinearMap.proj i).comp b.equivFun.toLinearMap)
  have hh := E.symm.contDiff.comp hc
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh

end PolycyclicRecognition

end

end OAI

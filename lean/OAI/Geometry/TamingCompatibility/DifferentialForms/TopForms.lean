import Mathlib

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.TopForms
open ContinuousAlternatingMap
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {n : ℕ}

def coefficient (b : Module.Basis (Fin n) ℝ E)
    (ν α : E [⋀^Fin n]→L[ℝ] ℝ) : ℝ := α b / ν b

lemma eval_eq_det_mul (b : Module.Basis (Fin n) ℝ E)
    (α : E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin n → E) : α v = α b * b.det v := by
  have he := congrArg (fun a : E [⋀^Fin n]→ₗ[ℝ] ℝ => a v)
    (AlternatingMap.eq_smul_basis_det b α.toAlternatingMap)
  exact he

lemma coefficient_smul (b : Module.Basis (Fin n) ℝ E)
    (ν α : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν b ≠ 0) : coefficient b ν α • ν = α := by
  ext v
  change (α b / ν b) * ν v = α v
  rw [eval_eq_det_mul b ν v,eval_eq_det_mul b α v]
  field_simp

lemma coefficient_smul_left (b : Module.Basis (Fin n) ℝ E)
    (ν : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν b ≠ 0) (r : ℝ) :
    coefficient b ν (r • ν) = r := by
  change (r * ν b) / ν b = r
  exact mul_div_cancel_right₀ r hν

lemma eval_ne_zero (b : Module.Basis (Fin n) ℝ E)
    (ν : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) : ν b ≠ 0 := by
  intro h
  apply hν
  ext v
  change ν v = 0
  rw [eval_eq_det_mul b ν v,h,zero_mul]

lemma coefficient_independent (b c : Module.Basis (Fin n) ℝ E)
    (ν α : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    coefficient b ν α = coefficient c ν α := by
  nth_rw 2 [← coefficient_smul b ν α (eval_ne_zero b ν hν)]
  rw [coefficient_smul_left c ν (eval_ne_zero c ν hν)]

lemma comp_ne_zero (L : E ≃L[ℝ] D) (ν : D [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    ν.compContinuousLinearMap L.toContinuousLinearMap ≠ 0 := by
  intro h
  apply hν
  ext v
  have he := congrArg (fun a : E [⋀^Fin n]→L[ℝ] ℝ => a (fun i => L.symm (v i))) h
  simpa only [compContinuousLinearMap_apply,ContinuousLinearEquiv.coe_coe,
    Function.comp_def,ContinuousLinearEquiv.apply_symm_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply] using he

lemma coefficient_comp (b : Module.Basis (Fin n) ℝ E) (c : Module.Basis (Fin n) ℝ D)
    (L : E ≃L[ℝ] D) (ν α : D [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    coefficient b (ν.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      coefficient c ν α := by
  have he := congrArg (fun a : D [⋀^Fin n]→L[ℝ] ℝ => a.compContinuousLinearMap L.toContinuousLinearMap)
    (coefficient_smul c ν α (eval_ne_zero c ν hν))
  have hes : (coefficient c ν α • ν).compContinuousLinearMap L.toContinuousLinearMap =
      coefficient c ν α • ν.compContinuousLinearMap L.toContinuousLinearMap := by ext v; rfl
  rw [hes] at he
  rw [← he,coefficient_smul_left b _ (eval_ne_zero b _ (comp_ne_zero L ν hν))]

end TamingCompatibility.TopForms

end

end OAI

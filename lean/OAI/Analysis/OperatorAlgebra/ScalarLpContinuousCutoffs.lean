import OAI.Analysis.OperatorAlgebra.ScalarLpStrongConvergence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-! Continuous functional calculus for scalar L² multiplication, in a form
that keeps pointwise cutoffs and their operator realizations connected. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology CStarAlgebra

namespace WeakPureInfiniteness

instance scalarBoundedContinuousCStarAlgebra :
    CommCStarAlgebra (BoundedContinuousFunction ℝ ℂ) where

instance scalarBoundedContinuousComplexCFC :
    ContinuousFunctionalCalculus ℂ (BoundedContinuousFunction ℝ ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

instance scalarBoundedContinuousRealCFC :
    ContinuousFunctionalCalculus ℝ (BoundedContinuousFunction ℝ ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

def boundedFunctionEval (t : ℝ) : BoundedContinuousFunction ℝ ℂ →⋆ₐ[ℂ] ℂ where
  toFun a := a t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def scalarCosine (r : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (Real.cos (r * t) : ℂ)) (by fun_prop) 1 (by
      intro t
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (r * t))

@[simp] lemma scalarCosine_apply (r t : ℝ) :
    scalarCosine r t = (Real.cos (r * t) : ℂ) := rfl

lemma scalarCosine_selfAdjoint (r : ℝ) : IsSelfAdjoint (scalarCosine r) := by
  change star (scalarCosine r) = scalarCosine r
  ext t
  simp only [BoundedContinuousFunction.coe_star, Pi.star_apply, scalarCosine_apply,
    Complex.star_def, Complex.conj_ofReal]

lemma scalarCosine_character (r : ℝ) :
    scalarCosine r = (2 : ℂ)⁻¹ •
      (BoundedRecovery.spectralCharacter r + star (BoundedRecovery.spectralCharacter r)) := by
  ext t
  simp only [scalarCosine_apply, BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_star,
    Pi.add_apply, Pi.star_apply, smul_eq_mul,
    BoundedRecovery.spectralCharacter_apply, Complex.exp_ofReal_mul_I,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma scalarCosine_cfc_apply (r t : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (scalarCosine r) t = (f (Real.cos (r * t)) : ℂ) := by
  have h := (boundedFunctionEval t).map_cfc f (scalarCosine r) hf.continuousOn
    (ha := scalarCosine_selfAdjoint r)
    (hφa := (scalarCosine_selfAdjoint r).map (boundedFunctionEval t))
  change (cfc f (scalarCosine r)) t = cfc f (scalarCosine r t) at h
  change (cfc f (scalarCosine r)) t =
    cfc f (algebraMap ℝ ℂ (Real.cos (r * t))) at h
  rw [cfc_algebraMap] at h
  exact h

lemma scalarLp_commute_cosine (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
    Lp ℂ 2 (volume : Measure ℝ)) (r : ℝ)
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume)) :
    Commute T (scalarLpRepresentation volume (scalarCosine r)) := by
  rw [scalarCosine_character, map_smul, map_add, map_star]
  have h₁ : Commute T (scalarLpRepresentation volume (BoundedRecovery.spectralCharacter r)) := by
    simpa only [scalarLpRepresentation_character] using hc r
  have h₂ : Commute T
      (scalarLpRepresentation volume (star (BoundedRecovery.spectralCharacter r))) := by
    rw [BoundedRecovery.spectralCharacter_star]
    simpa only [scalarLpRepresentation_character] using hc (-r)
  rw [map_star] at h₂
  exact (h₁.add_right h₂).smul_right _

lemma scalarLp_commute_cosine_cfc
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (r : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Commute T (scalarLpRepresentation volume (cfc f (scalarCosine r))) := by
  have : ContinuousFunctionalCalculus ℂ
      (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
      (A := Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
  have : ContinuousFunctionalCalculus ℝ
      (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
      (A := Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
  rw [(scalarLpRepresentation volume).map_cfc f (scalarCosine r) hf.continuousOn
    (ha := scalarCosine_selfAdjoint r)
    (hφa := (scalarCosine_selfAdjoint r).map (scalarLpRepresentation volume))]
  exact ((scalarLp_commute_cosine T r hc).symm.cfc_real f).symm

end WeakPureInfiniteness

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation
import Mathlib.Algebra.Lie.Ideal

namespace OAI

/-! # Invariance of Lie ideals under adjoint exponentials

Closed subspaces invariant under an operator are invariant under its
exponential, by the convergent power series. Together with the already
proved conjugation formula in a faithful representation, this proves
normality for the exponential images used by the Cartan construction.
-/

noncomputable section
namespace PolycyclicRecognition

section Operator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exp_apply_mem_of_stable (U : Submodule ℝ V) (hU : IsClosed (U : Set V))
    (A : V →L[ℝ] V) (hA : ∀ v ∈ U, A v ∈ U) {v : V} (hv : v ∈ U) :
    NormedSpace.exp A v ∈ U := by
  have hp (n : ℕ) : (A ^ n) v ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ']
      exact hA _ ih
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (ContinuousLinearMap.apply ℝ V v) (ContinuousLinearMap.apply ℝ V v).continuous
  have hs' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (A ^ n) v)
      (NormedSpace.exp A v) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, smul_apply] using hs
  rw [← hs'.tsum_eq]
  exact tsum_mem hU fun n => U.smul_mem _ (hp n)

end Operator

section LieIdeal

open Module LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance exponentialIdealNormedAddCommGroup : NormedAddCommGroup L :=
  generatorConjugationNormedAddCommGroup
local instance exponentialIdealNormedSpace : NormedSpace ℝ L := generatorConjugationNormedSpace

theorem exp_continuousAd_mem_ideal (I : LieIdeal ℝ L) (x : L) (t : ℝ)
    {v : L} (hv : v ∈ I) : NormedSpace.exp (t • continuousAd x) v ∈ I := by
  exact exp_apply_mem_of_stable I.toSubmodule I.toSubmodule.closed_of_finiteDimensional
    (t • continuousAd x) (fun y hy => I.smul_mem t (I.lie_mem hy)) hv

variable {G : Type*} [Group G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Normality follows from a faithful exponential-compatible representation
and surjectivity of the ambient exponential. No normality input is used. -/
theorem normal_of_exponential_ideal_representation
    (Exp : L → G) (hExp : Function.Surjective Exp)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (I : LieIdeal ℝ L) (S : Subgroup G)
    (hS : (S : Set G) = Exp '' (I : Set L)) : S.Normal := by
  constructor
  intro y hy g
  change y ∈ (S : Set G) at hy
  change g * y * g⁻¹ ∈ (S : Set G)
  rw [hS] at hy ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hExp g
  have heq := exp_ad_eq_group_conjugation Exp j ρ hρ hρExp x v 1
  simp only [one_smul] at heq
  rw [← heq]
  refine ⟨NormedSpace.exp (continuousAd x) v, ?_, rfl⟩
  change NormedSpace.exp (continuousAd x) v ∈ I
  simpa only [one_smul] using exp_continuousAd_mem_ideal I x 1 hv

end LieIdeal
end PolycyclicRecognition

end

end OAI

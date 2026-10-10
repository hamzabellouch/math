import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Brackets of generalized eigenvectors of a Lie endomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem lie_generalized_eigenvector_annihilated (A : L →ₗ⁅K⁆ L)
    (μ ν : K) (k l : ℕ) (x y : L)
    (hx : ((A.toLinearMap - μ • 1) ^ k) x = 0)
    (hy : ((A.toLinearMap - ν • 1) ^ l) y = 0) :
    ((A.toLinearMap - (μ * ν) • 1) ^ (k + l)) ⁅x, y⁆ = 0 := by
  induction k generalizing l x y with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ihk =>
    induction l generalizing x y with
    | zero =>
      have : y = 0 := by simpa using hy
      simp [this]
    | succ l ihl =>
      let Nμ := A.toLinearMap - μ • 1
      let Nν := A.toLinearMap - ν • 1
      let T := A.toLinearMap - (μ * ν) • 1
      have hx' : (Nμ ^ k) (Nμ x) = 0 := by
        simpa only [Nμ, pow_succ, Module.End.mul_apply] using hx
      have hy' : (Nν ^ l) (Nν y) = 0 := by
        simpa only [Nν, pow_succ, Module.End.mul_apply] using hy
      have hc : Commute Nν A.toLinearMap :=
        (Commute.refl A.toLinearMap).sub_left (Algebra.commute_algebraMap_left ν _)
      have hyA : (Nν ^ (l + 1)) (A y) = 0 := by
        have h := congrArg (fun F : Module.End K L => F y) (hc.pow_left (l + 1)).eq
        change (Nν ^ (l + 1)) (A y) = A ((Nν ^ (l + 1)) y) at h
        rw [h, hy, map_zero]
      have h₁ := ihk (l + 1) (Nμ x) (A y) hx' hyA
      have h₂ := ihl x (Nν y) hx hy'
      have hid : T ⁅x, y⁆ = ⁅Nμ x, A y⁆ + μ • ⁅x, Nν y⁆ := by
        change A ⁅x, y⁆ - (μ * ν) • ⁅x, y⁆ = _
        rw [A.map_lie]
        simp only [Nμ, Nν, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_lie, lie_sub, smul_lie, lie_smul,
          smul_sub, smul_smul]
        change ⁅A x, A y⁆ - (μ * ν) • ⁅x, y⁆ =
          (⁅A x, A y⁆ - μ • ⁅x, A y⁆) +
            (μ • ⁅x, A y⁆ - (μ * ν) • ⁅x, y⁆)
        abel
      change (T ^ (k + 1 + (l + 1))) ⁅x, y⁆ = 0
      rw [show k + 1 + (l + 1) = (k + (l + 1)) + 1 by omega,
        pow_succ, Module.End.mul_apply, hid, map_add, map_smul]
      have h₂' : (T ^ (k + (l + 1))) ⁅x, Nν y⁆ = 0 := by
        simpa only [T, show k + (l + 1) = k + 1 + l by omega] using h₂
      rw [h₁, h₂', smul_zero, add_zero]

theorem lie_mem_genEigenspace (A : L →ₗ⁅K⁆ L) (μ ν : K) (k l : ℕ)
    {x y : L} (hx : x ∈ Module.End.genEigenspace A.toLinearMap μ k)
    (hy : y ∈ Module.End.genEigenspace A.toLinearMap ν l) :
    ⁅x, y⁆ ∈ Module.End.genEigenspace A.toLinearMap (μ * ν) (k + l : ℕ) := by
  rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx hy ⊢
  exact lie_generalized_eigenvector_annihilated A μ ν k l x y hx hy

theorem lie_mem_maxGenEigenspace (A : L →ₗ⁅K⁆ L) (μ ν : K)
    {x y : L} (hx : x ∈ Module.End.maxGenEigenspace A.toLinearMap μ)
    (hy : y ∈ Module.End.maxGenEigenspace A.toLinearMap ν) :
    ⁅x, y⁆ ∈ Module.End.maxGenEigenspace A.toLinearMap (μ * ν) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨k + l, lie_generalized_eigenvector_annihilated A μ ν k l x y hk hl⟩

end PolycyclicRecognition

end

end OAI

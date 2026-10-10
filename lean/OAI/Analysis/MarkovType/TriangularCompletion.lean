import OAI.Analysis.MarkovType.TriangularLimitSeminorm
import OAI.Analysis.MarkovType.NormedC00
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

abbrev PreSpace (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :=
  NormedC00 (limitNorm s) (definite s hθ)

abbrev Space (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :=
  UniformSpace.Completion (PreSpace s hθ)

def ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    C00 →ₗ[ℝ] Space s hθ :=
  (UniformSpace.Completion.toComplₗᵢ : PreSpace s hθ →ₗᵢ[ℝ] Space s hθ).toLinearMap.comp
    (NormedC00.coefficients (limitNorm s) (definite s hθ)).symm.toLinearMap

@[simp] theorem norm_ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (a : C00) : ‖ofC00 s hθ a‖ = limitNorm s a := by
  change ‖((NormedC00.coefficients (limitNorm s) (definite s hθ)).symm a :
    UniformSpace.Completion (PreSpace s hθ))‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

def basis (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (i : ℕ) : Space s hθ :=
  ofC00 s hθ (C00.basis i)

theorem norm_basis_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (i : ℕ) :
    ‖basis s hθ i‖ ≤ 1 := by
  rw [basis, norm_ofC00]
  exact basis_bound s i

def preTail (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    StrongDual ℝ (PreSpace s hθ) :=
  ((tailForm θ j).comp
    (NormedC00.coefficients (limitNorm s) (definite s hθ)).toLinearMap).mkContinuous 1
      (by
        intro a
        change |tailForm θ j a| ≤ 1 * limitNorm s a
        simpa only [one_mul] using tailForm_le s a j)

def tail (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    StrongDual ℝ (Space s hθ) :=
  (preTail s hθ j).extend
    (UniformSpace.Completion.toComplL : PreSpace s hθ →L[ℝ] Space s hθ)

@[simp] theorem tail_ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (j : ℕ) (a : C00) : tail s hθ j (ofC00 s hθ a) = tailForm θ j a := by
  change (preTail s hθ j).extend _
    ((UniformSpace.Completion.toComplL : PreSpace s hθ →L[ℝ] Space s hθ)
      ((NormedC00.coefficients (limitNorm s) (definite s hθ)).symm a)) = _
  rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)]
  rfl

theorem norm_tail_le (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    ‖tail s hθ j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (tail s hθ j).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro a
  let b : C00 := (NormedC00.coefficients (limitNorm s) (definite s hθ)) a
  change ‖tail s hθ j (ofC00 s hθ b)‖ ≤ 1 * ‖ofC00 s hθ b‖
  rw [tail_ofC00, norm_ofC00, Real.norm_eq_abs, one_mul]
  exact tailForm_le s b j

@[simp] theorem pairing (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (i j : ℕ) : tail s hθ j (basis s hθ i) = if j ≤ i then θ else 0 := by
  rw [basis, tail_ofC00, tailForm_basis]

private theorem linearCombination_basis (s : ∀ n : ℕ, TriangularSystem X n θ)
    (hθ : 0 < θ) : Finsupp.linearCombination ℝ (basis s hθ) = ofC00 s hθ := by
  apply Finsupp.lhom_ext
  intro i b
  rw [Finsupp.linearCombination_single]
  change b • ofC00 s hθ (C00.basis i) = ofC00 s hθ (Finsupp.single i b)
  rw [← map_smul]
  congr 1
  simp only [C00.basis, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem dense_span_basis (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    Dense (Submodule.span ℝ (Set.range (basis s hθ)) : Set (Space s hθ)) := by
  have hd : Dense (Set.range ((↑) : PreSpace s hθ → Space s hθ)) :=
    UniformSpace.Completion.denseRange_coe
  apply hd.mono
  rintro z ⟨a, rfl⟩
  rw [← Finsupp.range_linearCombination, linearCombination_basis]
  refine ⟨(NormedC00.coefficients (limitNorm s) (definite s hθ)) a, ?_⟩
  rfl

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI

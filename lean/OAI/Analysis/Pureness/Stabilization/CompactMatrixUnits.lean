import OAI.Analysis.Pureness.Stabilization.CompactOperators
import Mathlib.Tactic.FinCases

namespace OAI
noncomputable section
open scoped Topology InnerProductSpace
namespace CuntzTrace

def standardVector (i : ℕ) : StandardHilbert := lp.single 2 i (1 : ℂ)
lemma inner_standardVector (i j : ℕ) : inner ℂ (standardVector i) (standardVector j) = if i=j then 1 else 0 := by
  simp [standardVector, lp.inner_single_left, Pi.single_apply]
lemma norm_standardVector (i : ℕ) : ‖standardVector i‖ = 1 := by
  simp [standardVector, lp.norm_single]

def compactMatrixUnit (i j : ℕ) : StandardCompacts :=
  ⟨InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j), rankOne_mem_compactOperators _ _⟩

@[simp] theorem compactMatrixUnit_star (i j : ℕ) : star (compactMatrixUnit i j) = compactMatrixUnit j i := by
  apply Subtype.ext
  exact InnerProductSpace.adjoint_rankOne _ _

@[simp] theorem compactMatrixUnit_mul (i j k l : ℕ) :
    compactMatrixUnit i j * compactMatrixUnit k l = if j=k then compactMatrixUnit i l else 0 := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j) ∘L
    InnerProductSpace.rankOne ℂ (standardVector k) (standardVector l) = _
  rw [InnerProductSpace.rankOne_comp_rankOne, inner_standardVector]
  split_ifs <;> simp_all [compactMatrixUnit]

@[simp] theorem compactMatrixUnit_norm (i j : ℕ) : ‖compactMatrixUnit i j‖ = 1 := by
  change ‖InnerProductSpace.rankOne ℂ (standardVector i) (standardVector j)‖ = 1
  rw [InnerProductSpace.norm_rankOne, norm_standardVector, norm_standardVector, one_mul]

def compactProjection (s : Finset ℕ) : StandardCompacts := ∑ i ∈ s, compactMatrixUnit i i

lemma compactProjection_star (s : Finset ℕ) : star (compactProjection s) = compactProjection s := by
  simp [compactProjection]
lemma compactProjection_mul (s : Finset ℕ) : compactProjection s * compactProjection s = compactProjection s := by
  classical
  simp [compactProjection, Finset.sum_mul, Finset.mul_sum]

theorem compactProjection_compress (s : Finset ℕ) (i j : ℕ) (hi : i ∈ s) (hj : j ∈ s) :
    compactProjection s * compactMatrixUnit i j * compactProjection s = compactMatrixUnit i j := by
  classical
  simp [compactProjection, Finset.sum_mul, Finset.mul_sum, hi, hj]
end CuntzTrace

end

end OAI

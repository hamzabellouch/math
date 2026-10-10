import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
namespace CuntzPureness
open Set
open scoped NNReal
variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

theorem continuous_nnreal_orthogonal_separators {K L : Set X}
    (hK : IsClosed K) (hL : IsClosed L) (hKL : Disjoint K L) :
    ∃ u v : C(X, ℝ≥0), (∀ x ∈ K, u x = 1) ∧ (∀ x ∈ L, v x = 1) ∧
      u ≤ 1 ∧ v ≤ 1 ∧ u*v = 0 := by
  obtain ⟨f,hfK,hfL,hf⟩ := exists_continuous_zero_one_of_isClosed hK hL hKL
  let u : C(X, ℝ≥0) := ⟨fun x => (1-3*f x).toNNReal,
    continuous_real_toNNReal.comp (continuous_const.sub (continuous_const.mul f.continuous))⟩
  let v : C(X, ℝ≥0) := ⟨fun x => (3*f x-2).toNNReal,
    continuous_real_toNNReal.comp ((continuous_const.mul f.continuous).sub continuous_const)⟩
  refine ⟨u,v,?_,?_,?_,?_,?_⟩
  · intro x hx
    change (1-3*f x).toNNReal = 1
    rw [hfK hx]
    norm_num
  · intro x hx
    change (3*f x-2).toNNReal = 1
    rw [hfL hx]
    norm_num
  · intro x
    change (1-3*f x).toNNReal ≤ 1
    rw [Real.toNNReal_le_iff_le_coe]
    have h := (hf x).1
    norm_num
    linarith
  · intro x
    change (3*f x-2).toNNReal ≤ 1
    rw [Real.toNNReal_le_iff_le_coe]
    have h := (hf x).2
    norm_num
    linarith
  · apply ContinuousMap.ext
    intro x
    change (1-3*f x).toNNReal * (3*f x-2).toNNReal = 0
    by_cases hx : 3*f x ≤ 1
    · rw [Real.toNNReal_eq_zero.mpr (by linarith : 3*f x-2 ≤ 0),mul_zero]
    · rw [Real.toNNReal_eq_zero.mpr (by linarith : 1-3*f x ≤ 0),zero_mul]
end CuntzPureness

end

end OAI

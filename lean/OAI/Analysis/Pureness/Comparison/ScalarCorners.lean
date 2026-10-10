import OAI.Analysis.Pureness.Comparison.FullnessFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace OAI
open scoped BigOperators
namespace CuntzComparison

section Algebra
variable {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype ι]

theorem finiteDimensional_of_scalar_corner_frame (p : A) (x : ι → A)
    (hframe : ∑ i, star (x i) * p * x i = 1)
    (hcorner : ∀ a : A, ∃ z : ℂ, p * a * p = z • p) :
    FiniteDimensional ℂ A := by
  classical
  let v : ι × ι → A := fun ij => star (x ij.1) * p * x ij.2
  refine ⟨⟨Finset.univ.image v, ?_⟩⟩
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply top_unique
  intro a ha
  choose c hc using fun i j => hcorner (x i * a * star (x j))
  have hexp : a = ∑ i, ∑ j, c i j • v (i, j) := by
    calc
      a = (∑ i, star (x i) * p * x i) * a * (∑ j, star (x j) * p * x j) := by
        rw [hframe]; simp
      _ = ∑ i, ∑ j, (star (x i) * p * x i * a) * (star (x j) * p * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = star (x i) * (p * (x i * a * star (x j)) * p) * x j := by simp only [mul_assoc]
          _ = c i j • v (i, j) := by rw [hc]; simp only [v, mul_smul_comm, smul_mul_assoc]
  rw [hexp]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
end Algebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteDimensional_of_scalar_corner [IsSimpleCStarAlgebra A]
    {p : A} (hp : 0 ≤ p) (hne : p ≠ 0)
    (hcorner : ∀ a : A, ∃ z : ℂ, p * a * p = z • p) :
    FiniteDimensional ℂ A := by
  obtain ⟨l, hl⟩ := exists_positive_fullness_frame hp hne
  apply finiteDimensional_of_scalar_corner_frame p l.get _ hcorner
  have hlist : List.ofFn (fun i => star (l.get i) * p * l.get i) =
      l.map (fun a => star a * p * a) := by
    change List.ofFn ((fun a : A => star a * p * a) ∘ l.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← List.sum_ofFn, hlist]
  exact hl

theorem exists_nonscalar_sandwich [IsSimpleCStarAlgebra A]
    (hinfinite : ¬ FiniteDimensional ℂ A) {p : A} (hp : 0 ≤ p) (hne : p ≠ 0) :
    ∃ a : A, ∀ z : ℂ, p * a * p ≠ z • p := by
  by_contra h
  push Not at h
  exact hinfinite (finiteDimensional_of_scalar_corner hp hne h)

end CuntzComparison

end OAI

import Mathlib

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum

variable {A : Type*} [CommRing A]
  (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
  (S : Subring A)

def subringGrade (n : ℕ) : Submodule ℤ S :=
  (𝒜 n).comap S.subtype.toAddMonoidHom.toIntLinearMap

theorem subringGrade_independent : iSupIndep (subringGrade 𝒜 S) := by
  have h := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  apply Subtype.ext
  apply (disjoint_iff_inf_le.mp (h i))
  refine ⟨hx.1, ?_⟩
  have hle : (⨆ j, ⨆ (_ : j ≠ i), subringGrade 𝒜 S j) ≤
      (⨆ j, ⨆ (_ : j ≠ i), 𝒜 j).comap S.subtype.toAddMonoidHom.toIntLinearMap := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact Submodule.comap_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  exact hle hx.2

theorem subringGrade_spans
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    (⨆ n, subringGrade 𝒜 S n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  let c : ℕ → S := fun n => ⟨decompose 𝒜 x.1 n, hS n x.1 x.2⟩
  have he : x = ∑ n ∈ (decompose 𝒜 x.1).support, c n := by
    apply Subtype.ext
    change x.1 = S.subtype (∑ n ∈ (decompose 𝒜 x.1).support, c n)
    rw [map_sum]
    exact (sum_support_decompose 𝒜 x.1).symm
  rw [he]
  apply Submodule.sum_mem
  intro n hn
  exact (le_iSup (subringGrade 𝒜 S) n) (show c n ∈ subringGrade 𝒜 S n from
    (decompose 𝒜 x.1 n).2)

@[instance_reducible]
def subringGradedAlgebra
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    GradedAlgebra (subringGrade 𝒜 S) where
  one_mem := show (1 : A) ∈ 𝒜 0 from SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j x y hx hy
    change (x.1 * y.1) ∈ 𝒜 (i + j)
    exact SetLike.mul_mem_graded hx hy
  toDecomposition :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (subringGrade_independent 𝒜 S) (subringGrade_spans 𝒜 S hS)).chooseDecomposition

end PiExponent

end

end OAI

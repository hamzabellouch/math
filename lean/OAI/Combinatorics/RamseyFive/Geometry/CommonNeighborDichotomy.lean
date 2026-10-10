import Mathlib

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem common_neighbor_dichotomy (A B C : Submodule K V)
    (hC : finrank K C = 3) (hAB : finrank K (A ⊓ B : Submodule K V) = 2)
    (hCA : finrank K (C ⊓ A : Submodule K V) = 2)
    (hCB : finrank K (C ⊓ B : Submodule K V) = 2) :
    A ⊓ B ≤ C ∨ C ≤ A ⊔ B := by
  by_cases h : A ⊓ B ≤ C
  · exact Or.inl h
  right
  have hi : C ⊓ (A ⊓ B) < A ⊓ B := lt_of_le_of_ne inf_le_right (by
    intro he
    apply h
    rw [← he]
    exact inf_le_left)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  rw [hAB] at hlt
  have he := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ A) (C ⊓ B)
  have hinf : (C ⊓ A) ⊓ (C ⊓ B) = C ⊓ (A ⊓ B) := by
    ext
    simp only [Submodule.mem_inf]
    tauto
  rw [hCA, hCB, hinf] at he
  have hle : (C ⊓ A) ⊔ (C ⊓ B) ≤ C := sup_le inf_le_left inf_le_left
  have hdim := Submodule.finrank_mono hle
  rw [hC] at hdim
  have heq : (C ⊓ A) ⊔ (C ⊓ B) = C :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [← heq]
  exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)

theorem finrank_sup_of_plane_intersection (A B : Submodule K V)
    (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hAB : finrank K (A ⊓ B : Submodule K V) = 2) :
    finrank K (A ⊔ B : Submodule K V) = 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hA, hB, hAB] at h
  omega

end SharpRamseyFive.RichPlaneOverlap

end OAI

import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexStarModule CStarAlgebra

open ComplexStarModule

namespace Kadison.BicommutantRange

variable {B : Type*} [CStarAlgebra B]

lemma eq_of_selfAdjoint_contractions (S : StarSubalgebra ℂ B)
    (h : ∀ T∈Set.centralizer (Set.centralizer (S : Set B)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈S) :
    Set.centralizer (Set.centralizer (S : Set B))=(S : Set B) := by
  have hs : ∀ T∈Set.centralizer (Set.centralizer (S : Set B)), IsSelfAdjoint T → T∈S := by
    intro T hT hsT
    by_cases hz : T=0
    · rw [hz]; exact S.zero_mem
    have hn : ‖T‖≠0 := norm_ne_zero_iff.mpr hz
    have hm : (‖T‖⁻¹:ℝ) • T∈Set.centralizer (Set.centralizer (S : Set B)) := by
      intro b hb
      simp only [mul_smul_comm,smul_mul_assoc,hT b hb]
    have hs' : IsSelfAdjoint ((‖T‖⁻¹:ℝ) • T) := (IsSelfAdjoint.all _).smul hsT
    have hnorm : ‖(‖T‖⁻¹:ℝ) • T‖≤1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg T)),inv_mul_cancel₀ hn]
    have hd := S.smul_mem (h _ hm hs' hnorm) (‖T‖:ℂ)
    simpa only [Complex.coe_smul,smul_smul,mul_inv_cancel₀ hn,one_smul] using hd
  let D := StarSubalgebra.centralizer ℂ ((StarSubalgebra.centralizer ℂ (S : Set B)) : Set B)
  have he : (D : Set B)=Set.centralizer (Set.centralizer (S : Set B)) := by
    simp only [D,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  apply Set.Subset.antisymm
  · intro T hT
    have hTD : T∈D := by rw [←SetLike.mem_coe,he]; exact hT
    let r : ℝ := 2⁻¹
    have hr : (ℜ T : B)∈D := by
      have h := D.smul_mem (D.add_mem hTD (D.star_mem' hTD)) (r:ℂ)
      rw [Complex.coe_smul] at h
      exact h
    have hi : (ℑ T : B)∈D := by
      have h := D.smul_mem (D.smul_mem (D.sub_mem hTD (D.star_mem' hTD)) (r:ℂ)) (-Complex.I)
      rw [Complex.coe_smul] at h
      exact h
    have hr' := hs (ℜ T) (by rw [←he]; exact hr) (ℜ T).property
    have hi' := hs (ℑ T) (by rw [←he]; exact hi) (ℑ T).property
    change T∈S
    have ht : (ℜ T:B)+Complex.I • (ℑ T:B)∈S := S.add_mem hr' (S.smul_mem hi' Complex.I)
    rw [realPart_add_I_smul_imaginaryPart] at ht
    exact ht
  · exact Set.subset_centralizer_centralizer

lemma starHom_range {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] B)
    (h : ∀ T∈Set.centralizer (Set.centralizer (Set.range φ)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈Set.range φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ :=
  eq_of_selfAdjoint_contractions φ.range h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorHom_range {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : ∀ T∈Set.centralizer (Set.centralizer (Set.range φ)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈Set.range φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ :=
  starHom_range φ h

def ofStarHom {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ) : VonNeumannAlgebra H where
  toStarSubalgebra := φ.range
  centralizer_centralizer' := hφ

end Kadison.BicommutantRange

end

end
end

end OAI

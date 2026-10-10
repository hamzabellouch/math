import Mathlib

namespace OAI

section
namespace ElementaryPositivity
attribute [local instance] Classical.propDecidable

lemma linearIndependent_of_filtered_dual {J V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : J → V) (degree : J → ℕ) (f : J → V →ₗ[ℚ] ℚ) (diag : J → ℚ)
    (hd : ∀ i,diag i ≠ 0)
    (hf : ∀ i j,degree j ≤ degree i → f i (v j)=if i=j then diag i else 0) :
    LinearIndependent ℚ v := by
  classical
  apply linearIndependent_iff.mpr
  intro l hl
  by_contra hn
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  obtain ⟨i,hi,hmax⟩ := l.support.exists_max_image degree hs
  have he := congrArg (f i) hl
  rw [map_zero,Finsupp.linearCombination_apply,Finsupp.sum] at he
  simp only [map_sum,map_smul,smul_eq_mul] at he
  have hh : (∑ j ∈ l.support,l j * f i (v j))=l i*diag i := by
    rw [Finset.sum_eq_single i]
    · rw [hf i i le_rfl,ite_eq_left rfl]
    · intro j hj hji
      rw [hf i j (hmax j hj),ite_eq_right (Ne.symm hji),mul_zero]
    · exact fun h=>False.elim (h hi)
  rw [hh] at he
  exact (Finsupp.mem_support_iff.mp hi) ((mul_eq_zero.mp he).resolve_right (hd i))

end ElementaryPositivity

end

end OAI

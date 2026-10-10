import Mathlib

namespace OAI

section

noncomputable section
open Set

namespace WeakMTWTransport

lemma exists_small_positive (S:Finset ℝ) (hS:∀a∈S,0<a) : ∃e:ℝ,0<e ∧ ∀a∈S,e≤a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨e,he,heS⟩:=ih (fun b hb=>hS b (Finset.mem_insert_of_mem hb))
    refine ⟨min a e,lt_min (hS a (Finset.mem_insert_self _ _)) he,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (heS b hb)

lemma ratio_mul_le {a e X A B:ℝ} (ha:a ≤ e*X) (hA:0 ≤ A) (hX:0 ≤ X)
    (he:e*A ≤ B) : a*A ≤ B*X := by
  calc a*A ≤ (e*X)*A := mul_le_mul_of_nonneg_right ha hA
       _ = (e*A)*X := by ring
       _ ≤ B*X := mul_le_mul_of_nonneg_right he hX

end WeakMTWTransport

end
end

end OAI

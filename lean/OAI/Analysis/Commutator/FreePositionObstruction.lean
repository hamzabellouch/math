import Mathlib
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

noncomputable section

namespace Kadison.FreeMoments

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)
  (hstar : ∀ a : A,τ (star a)=star (τ a))
  (hfaith : ∀ a : A,τ (star a*a)=0 → a=0)

include hstar hfaith in
theorem centered_intersection_zero (hfree : Free S τ) {i j : ι} (hij : i≠j)
    (a : A) (hi : a∈S i) (hj : a∈S j) (ha : τ a=0) : a=0 := by
  let l : Letter S τ := ⟨i,a,hi,ha⟩
  let r : Letter S τ := ⟨j,a,hj,ha⟩
  have h := gram_different_head hstar hfree (reduced_singleton l) (reduced_singleton r) hij
  apply hfaith
  simpa only [word_cons,word_nil,mul_one] using h

include hstar hfaith in
theorem intersection_scalar (h1 : τ 1=1) (hfree : Free S τ) {i j : ι} (hij : i≠j)
    (a : A) (hi : a∈S i) (hj : a∈S j) : a=τ a • (1:A) := by
  have hb : τ (a-τ a • (1:A))=0 := by simp [h1]
  have hzero := centered_intersection_zero S τ hstar hfaith hfree hij (a-τ a • (1:A))
    ((S i).sub_mem hi ((S i).smul_mem ((S i).one_mem) (τ a)))
    ((S j).sub_mem hj ((S j).smul_mem ((S j).one_mem) (τ a))) hb
  exact sub_eq_zero.mp hzero

include hstar hfaith in
theorem not_free_of_common_centered {i j : ι} (hij : i≠j)
    (a : A) (hi : a∈S i) (hj : a∈S j) (ha : τ a=0) (hne : a≠0) : ¬Free S τ := by
  intro hf
  exact hne (centered_intersection_zero S τ hstar hfaith hf hij a hi hj ha)

end Kadison.FreeMoments

namespace Kadison.FreeMoments

variable {A B ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable (S : ι → StarSubalgebra ℂ B) (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
  (j : A →⋆ₐ[ℂ] B) (htrace : ∀ a,ρ (j a)=τ a)
  (hstar : ∀ a : B,ρ (star a)=star (ρ a))
  (hfaith : ∀ a : A,τ (star a*a)=0 → a=0)

include htrace hstar hfaith in
omit [StarModule ℂ A] in
theorem mapped_centered_intersection_zero (hfree : Free S ρ) {i k : ι} (hik : i≠k)
    (a : A) (hi : j a∈S i) (hk : j a∈S k) (ha : τ a=0) : a=0 := by
  let l : Letter S ρ := ⟨i,j a,hi,(htrace a).trans ha⟩
  let r : Letter S ρ := ⟨k,j a,hk,(htrace a).trans ha⟩
  have h := gram_different_head hstar hfree (reduced_singleton l) (reduced_singleton r) hik
  have hz : ρ (star (j a)*j a)=0 := by
    simpa only [word_cons,word_nil,mul_one] using h
  apply hfaith
  rw [←map_star,←map_mul,htrace] at hz
  exact hz

include htrace hstar hfaith in
omit [StarModule ℂ A] in
theorem mapped_intersection_scalar (h1 : τ 1=1) (hfree : Free S ρ) {i k : ι} (hik : i≠k)
    (a : A) (hi : j a∈S i) (hk : j a∈S k) : a=τ a • (1:A) := by
  have hb : τ (a-τ a • (1:A))=0 := by simp [h1]
  have hm : j (a-τ a • (1:A))=j a-τ a • (1:B) := by simp
  have hz := mapped_centered_intersection_zero S τ ρ j htrace hstar hfaith hfree hik
    (a-τ a • (1:A))
    (hm ▸ (S i).sub_mem hi ((S i).smul_mem (S i).one_mem (τ a)))
    (hm ▸ (S k).sub_mem hk ((S k).smul_mem (S k).one_mem (τ a))) hb
  exact sub_eq_zero.mp hz

end Kadison.FreeMoments
end
end

end OAI

import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCompletion
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortInverse

namespace OAI

/-! Exact short/long splitting of the original finite inverse completion.
The short residue sum remains explicit, and vanishes at nonzero angular index. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryElementBall_filter_norm {C F : ℝ} (hCF : C ≤ F) :
    (primaryElementBall F).filter (fun c => norm c ≤ C) = primaryElementBall C := by
  ext c
  simp only [Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,_⟩,hn⟩
    exact ⟨hp,hn⟩
  · rintro ⟨hp,hn⟩
    exact ⟨⟨hp,hn.trans hCF⟩,hn⟩

theorem metaplectic_inverse_split (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B C F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F) (hCF : C ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 =
      metaplecticShortCompletionError r ℓ W U C+
        (∑ c ∈ primaryElementBall C, ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
          metaplecticMain r ℓ W (U/norm c^3))+
        metaplecticLongCompletion r ℓ W U C F := by
  let f : Eisenstein → ℂ := fun c =>
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      metaplecticCompleted r ℓ W (U/norm c^3)
  have hi : metaplecticAngularSmoothSum r ℓ W U 0 = ∑ c ∈ primaryElementBall F, f c := by
    rw [metaplectic_angular_actual_inverse r ℓ W hU hB hBF hW 0]
    simp only [metaplecticHeightCompleted_zero]
    rfl
  have hlong : (∑ c ∈ (primaryElementBall F).filter (fun c => ¬norm c ≤ C), f c) =
      metaplecticLongCompletion r ℓ W U C F := by
    rw [Finset.sum_filter]
    simp only [not_le,metaplecticLongCompletion,f]
  have hsplit := Finset.sum_filter_add_sum_filter_not (primaryElementBall F)
    (fun c => norm c ≤ C) f
  rw [primaryElementBall_filter_norm hCF,hlong] at hsplit
  rw [hi,←hsplit]
  congr 1
  rw [metaplecticShortCompletionError,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  dsimp [f]
  ring

theorem metaplectic_angular_inverse_split (r : Eisenstein) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) {U B C F : ℝ} (hU : 0 < U) (hB : 0 ≤ B)
    (hBF : B*U ≤ F) (hCF : C ≤ F) (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 =
      metaplecticShortCompletionError r ℓ W U C+metaplecticLongCompletion r ℓ W U C F := by
  rw [metaplectic_inverse_split r ℓ W hU hB hBF hCF hW]
  simp only [metaplecticMain,hℓ,ite_false,mul_zero,Finset.sum_const_zero,add_zero]

end CubicFirstMoment

end

end OAI

import OAI.MeasureTheory.Falconer.Geometry.ScalarClosureProjections
import OAI.MeasureTheory.Falconer.Geometry.ScalarNetIteration
import OAI.MeasureTheory.Falconer.Geometry.ScalarNormalizedCoefficients

namespace OAI

/-! The exact coefficient expressions used by the density normalization. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCoefficientClosure_mono {i j : ℕ} (hij : i ≤ j) (S : Finset ℝ) :
    scalarCoefficientClosure S i ⊆ scalarCoefficientClosure S j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step j _ ih => exact ih.trans (scalarCoefficientClosure_step S j)

 theorem scalar_coefficient_difference_mem (S : Finset ℝ) {x y : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) : y-x ∈ scalarCoefficientClosure S 2 := by
  have hx1 : -x ∈ scalarCoefficientClosure S 1 := by
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.neg_mem_neg hx))
  have hy1 := scalarCoefficientClosure_step S 0 hy
  have hm := Finset.add_mem_add hy1 hx1
  exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simpa [sub_eq_add_neg] using hm))

 theorem scalar_density_radius_mem {δ z R : ℝ} (E : Finset ℝ)
    (hcandidate : (z,R) ∈ scalarBallCandidates δ E) (hRδ : δ < R) :
    R ∈ scalarCoefficientClosure (E ∪ {1}) 3 := by
  let S := E ∪ {1}
  rcases Finset.mem_union.mp hcandidate with hp | hp
  · obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have heR : max δ |y-x| = R := congrArg Prod.snd he
    have hd : δ < |y-x| := by
      have hh : δ < max δ |y-x| := by rwa [heR]
      exact (lt_max_iff.mp hh).resolve_left (lt_irrefl _)
    have hdist : R = |y-x| := by simpa only [max_eq_right hd.le] using heR.symm
    rw [hdist]
    have hmem := scalar_coefficient_difference_mem S
      (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy)
    by_cases hnonneg : 0 ≤ y-x
    · rw [abs_of_nonneg hnonneg]
      exact scalarCoefficientClosure_step S 2 hmem
    · rw [abs_of_neg (lt_of_not_ge hnonneg)]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.neg_mem_neg hmem))
  · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hp
    have heR : (2:ℝ) = R := congrArg Prod.snd he
    rw [← heR]
    have h1 : (1:ℝ) ∈ S := Finset.mem_union_right _ (by simp)
    have h2 : (2:ℝ) ∈ scalarCoefficientClosure S 1 := by
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by
        rw [show (2:ℝ) = 1+1 by norm_num]
        exact Finset.add_mem_add h1 h1))
    exact scalarCoefficientClosure_mono (by omega) S h2

 theorem scalar_normalized_expression_mem {S : Finset ℝ} {a z R : ℝ}
    (ha : a ∈ S) (hz : z ∈ S) (hR : R⁻¹ ∈ S)
    (hhalf : (1/2:ℝ) ∈ S) (hsix : (1/6:ℝ) ∈ S) :
    (a-(z-3*R))/(6*R) ∈ scalarCoefficientClosure S 5 := by
  by_cases hR0 : R = 0
  · subst R
    simp only [mul_zero,div_zero]
    have hz0 : (0:ℝ) ∈ scalarCoefficientClosure S 2 := by
      simpa using scalar_coefficient_difference_mem S ha ha
    exact scalarCoefficientClosure_mono (by omega) S hz0
  have hd := scalar_coefficient_difference_mem S hz ha
  have hR2 := scalarCoefficientClosure_mono (show 0 ≤ 2 by omega) S hR
  have hm3 : (a-z)*R⁻¹ ∈ scalarCoefficientClosure S 3 :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mul_mem_mul hd hR2))
  have h63 := scalarCoefficientClosure_mono (show 0 ≤ 3 by omega) S hsix
  have hm4 : ((a-z)*R⁻¹)*(1/6:ℝ) ∈ scalarCoefficientClosure S 4 :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mul_mem_mul hm3 h63))
  have hh4 := scalarCoefficientClosure_mono (show 0 ≤ 4 by omega) S hhalf
  have hs5 : ((a-z)*R⁻¹)*(1/6:ℝ)+1/2 ∈ scalarCoefficientClosure S 5 :=
    Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.add_mem_add hm4 hh4))
  convert hs5 using 1
  field_simp
  ring

end Falconer

end OAI

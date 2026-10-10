import OAI.NumberTheory.Ostmann.HybridSieve.SamplingIntervals

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann.HybridSieve

theorem family_separated_samples_le_integral {κ ι : Type*} [Fintype κ] [Fintype ι]
    (character : ι → κ) (γ : ι → ℝ) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : ℝ) (hH : 1 ≤ H) (hγ : ∀ j, |γ j| ≤ H)
    (hsep : ∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|)
    (f g : κ → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (hderiv : ∀ i t, HasDerivAt (f i) (g i t) t) :
    (∑ j, w (character j) * ‖f (character j) (γ j)‖ ^ 2) ≤
      2 * (∑ i, w i * (∫ t in Icc (-2 * H) (2 * H), ‖f i t‖ ^ 2)) +
        (∑ i, w i * (∫ t in Icc (-2 * H) (2 * H), ‖g i t‖ ^ 2)) := by
  classical
  have hsum : (∑ j, w (character j) * ‖f (character j) (γ j)‖ ^ 2) =
      ∑ i, w i * ∑ j : {j // character j = i}, ‖f i (γ j)‖ ^ 2 := by
    rw [← Fintype.sum_fiberwise character (fun j => w (character j) * ‖f (character j) (γ j)‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [j.property]
  rw [hsum]
  calc
    _ ≤ ∑ i, w i *
        (2 * (∫ t in Icc (-2 * H) (2 * H), ‖f i t‖ ^ 2) +
          (∫ t in Icc (-2 * H) (2 * H), ‖g i t‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply separated_complex_samples_le_integral (fun j : {j // character j = i} => γ j)
        H hH (fun j => hγ j) ?_ (f i) (g i) (hf i) (hg i) (hderiv i)
      intro j k hjk
      exact hsep j k (fun h => hjk (Subtype.ext h)) (j.property.trans k.property.symm)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Ostmann.HybridSieve

end OAI

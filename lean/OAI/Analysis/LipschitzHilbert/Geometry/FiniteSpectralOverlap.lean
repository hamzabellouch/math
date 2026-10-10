import OAI.Analysis.LipschitzHilbert.Fourier.BandOrthogonality

namespace OAI

/-! Energy of a packet sum with finite spectral overlap. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem norm_sum_square_le_of_overlap {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (M : ℕ)
    (hM : (Finset.univ.filter (fun j => v j ≠ 0)).card ≤ M) :
    ‖∑ j, v j‖ ^ 2 ≤ M * ∑ j, ‖v j‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun j => v j ≠ 0)
  have hv : (∑ j ∈ s, v j) = ∑ j, v j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
  have he : (∑ j ∈ s, ‖v j‖ ^ 2) = ∑ j, ‖v j‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : v j = 0 := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
    simp [hz]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun j => ‖v j‖) (f := fun _ => (1 : ℝ)) (g := fun j => ‖v j‖ ^ 2)
    (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2
  rw [hv] at hn
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [he] at hcs
  exact (hn.trans hcs).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hM)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem finite_spectral_overlap_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (M : ℕ)
    (hM : ∀ ξ, (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let F : SchwartzMap ℝ ℂ := ∑ j, f j
  have hsum (x : ℝ) : F x = ∑ j, f j x := by simp [F]
  have hf (ξ : ℝ) : 𝓕 F ξ = ∑ j, 𝓕 (f j) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ j, f j)) ξ = _
    rw [map_sum]
    simp
  have hi : Integrable (fun ξ => ∑ j, ‖𝓕 (f j) ξ‖ ^ 2) volume :=
    integrable_finsetSum _ (fun j _ => ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
  calc
    _ = ∫ ξ, ‖𝓕 F ξ‖ ^ 2 := by
      rw [SchwartzMap.integral_norm_sq_fourier]
      simp only [hsum]
    _ ≤ ∫ ξ, (M : ℝ) * ∑ j, ‖𝓕 (f j) ξ‖ ^ 2 := by
      apply integral_mono (((𝓕 F).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) (hi.const_mul M)
      intro ξ
      dsimp only
      rw [hf]
      exact norm_sum_square_le_of_overlap _ M (hM ξ)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [SchwartzMap.integral_norm_sq_fourier]
      · intro j _
        exact ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)

end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Trees.FourGridBandErrors

namespace OAI

/-! Exact energy orthogonality of the separated annuli used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem norm_sum_square_of_disjoint {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (v : ι → E)
    (h : ∀ j k, j ≠ k → v j = 0 ∨ v k = 0) :
    ‖∑ j, v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
  classical
  by_cases hz : ∀ j, v j = 0
  · simp [hz]
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    have ho (k : ι) (hkj : k ≠ j) : v k = 0 := (h k j hkj).resolve_right hj
    rw [Finset.sum_eq_single j (fun k _ hkj => ho k hkj) (fun hj => (hj (Finset.mem_univ j)).elim)]
    rw [Finset.sum_eq_single j (fun k _ hkj => by rw [ho k hkj]; simp)
      (fun hj => (hj (Finset.mem_univ j)).elim)]

theorem bandOuter_lt_bandInner {j k : ℕ} (hjk : j < k) : bandOuter j < bandInner k := by
  unfold bandOuter bandInner
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mpr
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.succ_le_of_lt hjk)
  rw [pow_succ] at h
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) j]

theorem separated_band_fourier {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (hlow : ∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (ξ : ℝ) (j k : Fin N) (hjk : j ≠ k) : 𝓕 (f j) ξ = 0 ∨ 𝓕 (f k) ξ = 0 := by
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · by_cases h : |ξ| < bandInner k.val
    · exact Or.inr (hlow k ξ h)
    · exact Or.inl (hhigh j ξ ((bandOuter_lt_bandInner hjk).trans_le (le_of_not_gt h)))
  · by_cases h : |ξ| < bandInner j.val
    · exact Or.inl (hlow j ξ h)
    · exact Or.inr (hhigh k ξ ((bandOuter_lt_bandInner hkj).trans_le (le_of_not_gt h)))

theorem separated_band_energy {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (hlow : ∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) = ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let F : SchwartzMap ℝ ℂ := ∑ j, f j
  have hsum (x : ℝ) : F x = ∑ j, f j x := by simp [F]
  have hf (ξ : ℝ) : 𝓕 F ξ = ∑ j, 𝓕 (f j) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ j, f j)) ξ = _
    rw [map_sum]
    simp
  calc
    _ = ∫ x, ‖F x‖ ^ 2 := by simp only [hsum]
    _ = ∫ ξ, ‖𝓕 F ξ‖ ^ 2 := (SchwartzMap.integral_norm_sq_fourier F).symm
    _ = ∫ ξ, ∑ j, ‖𝓕 (f j) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hf, norm_sum_square_of_disjoint _ (separated_band_fourier f hlow hhigh ξ)]
    _ = ∑ j, ∫ ξ, ‖𝓕 (f j) ξ‖ ^ 2 :=
      integral_finsetSum _ (fun j _ => ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
    _ = _ := by simp only [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Geometry.FiniteSpectralOverlap

namespace OAI

/-! The spectral overlap count for fixed-width annuli at radix-four scales. -/

noncomputable section

open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem geometric_spectral_overlap {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (ξ : ℝ) : (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => 𝓕 (f j) ξ ≠ 0)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hm0 : 𝓕 (f m) ξ ≠ 0 := (Finset.mem_filter.mp hm).2
    have hmupper : |ξ| ≤ b * (4 : ℝ) ^ m.val := by
      by_contra h
      exact hm0 (hhigh m ξ (lt_of_not_ge h))
    have hinterval (j : Fin N) (hj : j ∈ s) : j.val ∈ Finset.Ico m.val (m.val + M) := by
      have hlo : m ≤ j := Finset.min'_le s j hj
      have hj0 : 𝓕 (f j) ξ ≠ 0 := (Finset.mem_filter.mp hj).2
      have hjlower : a * (4 : ℝ) ^ j.val ≤ |ξ| := by
        by_contra h
        exact hj0 (hlow j ξ (lt_of_not_ge h))
      have hhi : j.val < m.val + M := by
        by_contra h
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (le_of_not_gt h)
        have hprod := mul_le_mul_of_nonneg_left hp ha.le
        rw [pow_add] at hprod
        have hsep' := mul_lt_mul_of_pos_right hsep
          (pow_pos (by norm_num : (0 : ℝ) < 4) m.val)
        nlinarith [hprod]
      exact Finset.mem_Ico.mpr ⟨hlo,hhi⟩
    have hsubset : s.image (fun j : Fin N => j.val) ⊆ Finset.Ico m.val (m.val + M) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact hinterval j hj
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_image_of_injective s Fin.val_injective, Nat.card_Ico] at hcard
    simpa only [Nat.add_sub_cancel_left] using hcard
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ M
    simp [he]

theorem geometric_annular_energy {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 :=
  finite_spectral_overlap_energy f M (geometric_spectral_overlap f ha hsep hlow hhigh)

end LipschitzHilbert

end

end OAI

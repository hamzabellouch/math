import OAI.NumberTheory.Ostmann.Characters.CharacterPageComparison

namespace OAI

/-! # Uniform kernel bounds for the canonical exceptional zeros

For large conductors the Page cutoff is to the right of one half. The
remaining finitely many moduli contribute a finite constant.
-/

namespace Ostmann

open Complex

noncomputable def pageRieszKernelNorm (q : ℕ) : ℝ :=
  ‖rieszMellinKernel (pageBeta (actualLocalZero q) : ℂ)‖

theorem page_beta_half_for_large_modulus : ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
    1 / 2 ≤ pageBeta (actualLocalZero q) := by
  let N := ⌈Real.exp (2 * actualPageConstant)⌉₊ + 1
  refine ⟨N, ?_⟩
  intro q hq
  have hqpos : 1 ≤ q := by dsimp [N] at hq; omega
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have he : Real.exp (2 * actualPageConstant) ≤ (q : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (2 * actualPageConstant)⌉₊ ≤ q by dsimp [N] at hq; omega))
  have hL : 2 * actualPageConstant ≤ Real.log (4 * (q : ℝ)) :=
    (Real.le_log_iff_exp_le (by linarith : 0 < 4 * (q : ℝ))).mpr (he.trans (by linarith))
  have hLp : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hfrac : actualPageConstant / Real.log (4 * (q : ℝ)) ≤ 1 / 2 :=
    (div_le_iff₀ hLp).mpr (by linarith)
  cases heq : actualLocalZero q with
  | none => norm_num [pageBeta]
  | some e =>
    have hb := (actualLocalZero_spec q e heq).2
    change 1 / 2 ≤ e.beta
    linarith

theorem canonical_riesz_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, pageRieszKernelNorm q ≤ C := by
  classical
  obtain ⟨N, hN⟩ := page_beta_half_for_large_modulus
  let S := ∑ q ∈ Finset.range N, pageRieszKernelNorm q
  have hS : 0 ≤ S := Finset.sum_nonneg (fun q _ => norm_nonneg _)
  refine ⟨10 + S, by positivity, ?_⟩
  intro q
  by_cases hq : N ≤ q
  · have hh := rieszMellinKernel_half_strip (pageBeta (actualLocalZero q) : ℂ)
      (by simpa using hN q hq)
    have hk : pageRieszKernelNorm q ≤ 9 := by
      simpa [pageRieszKernelNorm, rieszLineMajorant] using hh
    linarith
  · have hs : pageRieszKernelNorm q ≤ S := Finset.single_le_sum (f := pageRieszKernelNorm) (a := q)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_of_not_ge hq))
    linarith

theorem canonicalCharacterRieszTerm_norm_bound (χ : PrimitiveComplexCharacter)
    (q : ℕ) (X C : ℝ) (hX : 0 < X) (hC : 0 ≤ C)
    (hbound : pageRieszKernelNorm q ≤ C) :
    ‖canonicalCharacterRieszTerm χ q X‖ ≤ C * X ^ pageBeta (actualLocalZero q) := by
  classical
  cases he : actualLocalZero q with
  | none => simp only [canonicalCharacterRieszTerm, he, norm_zero, pageBeta]; positivity
  | some e =>
    by_cases hc : e.asRealCharacter.asComplex = χ
    · simp only [canonicalCharacterRieszTerm, he, hc, ↓reduceIte, norm_neg,
        rieszContourWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.ofReal_re, pageBeta]
      have hh : ‖rieszMellinKernel (e.beta : ℂ)‖ ≤ C := by
        simpa only [pageRieszKernelNorm, he, pageBeta] using hbound
      nlinarith [Real.rpow_pos_of_pos hX e.beta]
    · simp only [canonicalCharacterRieszTerm, he, hc, ↓reduceIte, norm_zero, pageBeta]
      positivity

end Ostmann

end OAI

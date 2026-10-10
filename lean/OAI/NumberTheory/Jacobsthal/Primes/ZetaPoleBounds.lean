import OAI.NumberTheory.Jacobsthal.Sieve.PrincipalEulerCorrection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex

noncomputable abbrev regularZeta := DirichletCharacter.LFunctionTrivChar₁ 1

lemma neg_logDeriv_zeta_pole_split {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s = -logDeriv regularZeta s + 1/(s-1) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  simp only [logDeriv_apply, regularZeta]
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1]
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  field_simp
  ring

theorem exists_regular_zeta_compact_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ 6 →
      ‖logDeriv regularZeta s‖ ≤ C := by
  let K : Set ℂ := Icc (1:ℝ) 2 ×ℂ Icc (-6:ℝ) 6
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun s => -deriv regularZeta s / regularZeta s) K := by
    apply (DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono
    intro s hs
    right
    have hr : 1 ≤ s.re := ((Complex.mem_reProdIm.mp hs).1).1
    simpa only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq] using
      riemannZeta_ne_zero_of_one_le_re hr
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs hs2 ht
  have hm : s ∈ K := ⟨⟨hs,hs2⟩,abs_le.mp ht⟩
  have h := (hC s hm).trans (le_max_right (1:ℝ) C)
  simpa only [logDeriv_apply, neg_div, norm_neg] using h

theorem exists_zeta_small_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 6 →
      (-logDeriv riemannZeta s).re ≤ C+(1/(s-1)).re := by
  obtain ⟨C,hC,hbound⟩ := exists_regular_zeta_compact_bound
  refine ⟨C,hC,?_⟩
  intro s hs hs2 ht
  rw [neg_logDeriv_zeta_pole_split hs, Complex.add_re]
  have h := (Complex.re_le_norm (-logDeriv regularZeta s)).trans
    (by simpa only [norm_neg] using hbound s hs.le hs2 ht)
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI

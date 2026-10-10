import OAI.NumberTheory.Jacobsthal.Estimates.RieszIntegrand

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex

lemma modulusHeight_le_of_abs_le (q : ℕ) (T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) :
    modulusHeight q t ≤ modulusHeight q T := by
  have h := Real.log_le_log (by positivity : 0 < |t|+6) (by linarith : |t|+6 ≤ T+6)
  unfold modulusHeight
  rw [abs_of_nonneg hT]
  linarith

noncomputable def rieszContourLeft (a : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  1-a/(modulusHeight q T)^2
noncomputable def rieszContourRectangle (a : ℝ) (q : ℕ) (sigma T : ℝ) : Set ℂ :=
  Icc (rieszContourLeft a q T) sigma ×ℂ Icc (-T) T

theorem exists_uniform_riesz_rectangle :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ X sigma T : ℝ, 0 < X → 1 < sigma → sigma ≤ 2 → 0 < T →
        1/2 ≤ rieszContourLeft a q T ∧
        (∀ s ∈ rieszContourRectangle a q sigma T,
          DirichletCharacter.LFunction chi s ≠ 0 ∧
          ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3) ∧
        _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (rieszContourRectangle a q sigma T) := by
  obtain ⟨a,ha,ha100,C,hC,hstrip⟩ := exists_uniform_nonprincipal_strip_bound
  refine ⟨a,ha,ha100,C,hC,?_⟩
  intro q _ chi hchi X sigma T hX _hs hs2 hT
  have hH := modulusHeight_ge_one q T
  have hHp : 0 < modulusHeight q T := by linarith
  have hHsq : 1 ≤ (modulusHeight q T)^2 := by nlinarith
  have hfrac : a/(modulusHeight q T)^2 ≤ a := by
    apply (div_le_iff₀ (by positivity : 0 < (modulusHeight q T)^2)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hHsq ha.le
  have hleft : 1/2 ≤ rieszContourLeft a q T := by unfold rieszContourLeft; linarith
  have hb : ∀ s ∈ rieszContourRectangle a q sigma T,
      DirichletCharacter.LFunction chi s ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3 := by
    intro s hmem
    have hr := (Complex.mem_reProdIm.mp hmem).1
    have hi := (Complex.mem_reProdIm.mp hmem).2
    have hht := modulusHeight_le_of_abs_le q T hT.le (abs_le.mpr hi)
    have hHs := modulusHeight_ge_one q s.im
    have hHsp : 0 < modulusHeight q s.im := by linarith
    have hpow : (modulusHeight q s.im)^2 ≤ (modulusHeight q T)^2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_left ha.le (show 0 < (modulusHeight q s.im)^2 by positivity) hpow
    have hs' : 1-a/(modulusHeight q s.im)^2 ≤ s.re := by
      change 1-a/(modulusHeight q T)^2 ≤ s.re ∧ s.re ≤ sigma at hr
      linarith
    have h := hstrip q chi hchi s.re s.im hs' (hr.2.trans hs2)
    simp only [Complex.re_add_im] at h
    refine ⟨h.1,?_⟩
    change ‖deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s‖ ≤ _
    apply h.2.trans
    gcongr
  refine ⟨hleft,hb,?_⟩
  intro s hmem
  have hr := (Complex.mem_reProdIm.mp hmem).1.1
  have hsp : 0 < s.re := by linarith
  exact (differentiableAt_characterRieszIntegrand chi hchi hX hsp (hb s hmem).1).differentiableWithinAt

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI

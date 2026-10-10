import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.PrimeGaps.PrincipalGrowth

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma regularZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : regularZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
  · rw [regularZeta, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs)

lemma norm_inv_regularZeta_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(regularZeta s)⁻¹‖ ≤ absoluteZetaTwo := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := norm_inv_LFunction_le_absoluteZetaTwo (1 : DirichletCharacter ℂ 1) hs
  rw [DirichletCharacter.LFunction_modOne_eq] at hz
  have hn : 1 ≤ ‖s - 1‖ := by
    have h := Complex.re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  rw [regularZeta, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
    mul_inv_rev, norm_mul]
  simp only [norm_inv] at hz ⊢
  exact (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hn)
    (inv_nonneg.mpr (norm_nonneg (riemannZeta s)))).trans (by simpa using hz)

lemma exists_regularZeta_polynomial_growth :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 3 / 4 ≤ s.re →
      ‖regularZeta s‖ ≤ K * (‖s‖ + 2) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := LargePrimeGaps.zetaRegular_bounds
    (ε := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K + 1, by linarith, ?_⟩
  intro s hs
  have hreg := (hb s (by linarith)).1
  norm_num at hreg
  have he : regularZeta s = (s - 1) * LargePrimeGaps.zetaRegular s + 1 :=
    LargePrimeGaps.poleRemovedZeta_eq (by linarith)
  have hn : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1 : ℂ)
  rw [he]
  calc
    _ ≤ ‖s - 1‖ * ‖LargePrimeGaps.zetaRegular s‖ + 1 := by
      simpa only [norm_mul, norm_one] using norm_add_le ((s - 1) * LargePrimeGaps.zetaRegular s) 1
    _ ≤ (‖s‖ + 1) * (K * (‖s‖ + 2)) + 1 := by gcongr
    _ ≤ (K + 1) * (‖s‖ + 2) ^ 2 := by nlinarith [norm_nonneg s]

noncomputable def zetaCenter (t : ℝ) : ℂ := 2 + (t : ℂ) * Complex.I
noncomputable def zetaDiskPoint (t : ℝ) (w : ℂ) : ℂ := zetaCenter t + (5 / 4 : ℂ) * w
noncomputable def normalizedZeta (t : ℝ) (w : ℂ) : ℂ :=
  regularZeta (zetaDiskPoint t w) / regularZeta (zetaCenter t)

@[simp] lemma zetaCenter_re (t : ℝ) : (zetaCenter t).re = 2 := by simp [zetaCenter]
@[simp] lemma zetaDiskPoint_re (t : ℝ) (w : ℂ) :
    (zetaDiskPoint t w).re = 2 + (5 / 4 : ℝ) * w.re := by simp [zetaDiskPoint]

lemma zetaDiskPoint_quarter_strip (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    3 / 4 ≤ (zetaDiskPoint t w).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  rw [zetaDiskPoint_re]
  linarith

lemma zetaDiskPoint_norm (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖zetaDiskPoint t w‖ + 2 ≤ |t| + 6 := by
  have hc : ‖zetaCenter t‖ ≤ 2 + |t| := by
    simpa [zetaCenter, norm_mul] using norm_add_le (2 : ℂ) ((t : ℂ) * Complex.I)
  have h := norm_add_le (zetaCenter t) ((5 / 4 : ℂ) * w)
  have hn : ‖(5 / 4 : ℂ) * w‖ = (5 / 4 : ℝ) * ‖w‖ := by rw [norm_mul]; norm_num
  rw [hn] at h
  change ‖zetaDiskPoint t w‖ ≤ _ at h
  linarith

lemma normalizedZeta_zero (t : ℝ) : normalizedZeta t 0 = 1 := by
  unfold normalizedZeta zetaDiskPoint
  simp only [mul_zero, add_zero]
  exact div_self (regularZeta_ne_zero_of_one_le_re (by simp))

lemma normalizedZeta_analytic (t : ℝ) (w : ℂ) : AnalyticAt ℂ (normalizedZeta t) w := by
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hd : Differentiable ℂ (normalizedZeta t) := by
    unfold normalizedZeta zetaDiskPoint regularZeta
    fun_prop
  exact hd.analyticAt w

lemma normalizedZeta_zero_re_lt (t : ℝ) {w : ℂ} (hw : normalizedZeta t w = 0) :
    w.re < -4 / 5 := by
  have hn := regularZeta_ne_zero_of_one_le_re (s := zetaCenter t) (by simp)
  have hz : regularZeta (zetaDiskPoint t w) = 0 := (div_eq_zero_iff.mp hw).resolve_right hn
  by_contra! h
  have hre : 1 ≤ (zetaDiskPoint t w).re := by rw [zetaDiskPoint_re]; linarith
  exact regularZeta_ne_zero_of_one_le_re hre hz

lemma exists_normalizedZeta_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (t : ℝ) (w : ℂ), ‖w‖ ≤ 1 →
      ‖normalizedZeta t w‖ ≤ K * (|t| + 6) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := exists_regularZeta_polynomial_growth
  have hB := one_le_absoluteZetaTwo
  refine ⟨K * absoluteZetaTwo, by nlinarith, ?_⟩
  intro t w hw
  have hg := hb (zetaDiskPoint t w) (zetaDiskPoint_quarter_strip t hw)
  have hi := norm_inv_regularZeta_le (s := zetaCenter t) (by simp)
  unfold normalizedZeta
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (K * (‖zetaDiskPoint t w‖ + 2) ^ 2) * absoluteZetaTwo :=
      mul_le_mul hg hi (norm_nonneg _) (by positivity)
    _ ≤ (K * (|t| + 6) ^ 2) * absoluteZetaTwo := by
      have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖zetaDiskPoint t w‖ + 2)
        (zetaDiskPoint_norm t hw) 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by linarith)) (by positivity)
    _ = _ := by ring

end Ostmann.Dirichlet

end OAI

import OAI.NumberTheory.Ostmann.Dirichlet.PrincipalHeightBound

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma real_pole_bound_away_from_zero_sharp (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {c sigma t : ℝ} (hc : 0 < c) (hs : 1 < sigma) (_hs2 : sigma ≤ 2)
    (ht : c/(2*Real.log (q:ℝ)) ≤ |t|) :
    (1/(((sigma:ℂ)+(2*t:ℝ)*Complex.I)-1)).re ≤
      (sigma-1)*(modulusHeight q t)^2/c^2 := by
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
  have htpos : 0 < |t| := (div_pos hc (by positivity)).trans_le ht
  have htne : t ≠ 0 := abs_pos.mp htpos
  have htsq : 0 < 4*t^2 := by positivity
  have hc2 : 0 < c^2 := by positivity
  have hct : c ≤ 2*Real.log (q:ℝ)*|t| := by
    have h := (div_le_iff₀ (show 0 < 2*Real.log (q:ℝ) by positivity)).mp ht
    nlinarith only [h]
  have hcSq : c^2 ≤ 4*(Real.log (q:ℝ))^2*t^2 := by
    have h : c^2 ≤ (2*Real.log (q:ℝ)*|t|)^2 := by gcongr
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hp : Real.log (q:ℝ) ≤ modulusHeight q t := by
    have hh : 0 ≤ Real.log (|t|+6) := Real.log_nonneg (by have := abs_nonneg t; linarith)
    unfold modulusHeight
    linarith
  have hsq : (Real.log (q:ℝ))^2 ≤ (modulusHeight q t)^2 := by gcongr
  rw [zetaPole_real_eq]
  have hr : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).re = sigma := by simp
  have hi : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t := by simp
  rw [hr, hi]
  calc
    _ ≤ (sigma-1)/(4*t^2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (sigma-1)^2+(2*t)^2) htsq).mpr
      nlinarith only [sq_nonneg (sigma-1), show 0 < sigma-1 by linarith]
    _ ≤ (sigma-1)*((Real.log (q:ℝ))^2/c^2) := by
      have hdiv : 1/(4*t^2) ≤ (Real.log (q:ℝ))^2/c^2 :=
        (div_le_div_iff₀ htsq hc2).mpr (by nlinarith only [hcSq])
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left hdiv (show 0 ≤ sigma-1 by linarith)
    _ ≤ (sigma-1)*((modulusHeight q t)^2/c^2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hc2.le) (by linarith)
    _ = _ := by ring

theorem exists_quadratic_zero_reciprocal_bound_sharp (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi^2 = 1 →
      ∀ sigma beta t : ℝ, 1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      c/(2*Real.log (q:ℝ)) ≤ |t| →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      4/(sigma-beta) ≤ 3/(sigma-1)+K*modulusHeight q t+
        (sigma-1)*(modulusHeight q t)^2/c^2 := by
  obtain ⟨Cp,hCp,hpen⟩ := uniform_zero_penalty
  obtain ⟨Cu,hCu,hprincipal⟩ := exists_principal_all_height_log_bound
  obtain ⟨Cz,hCz,hzeta⟩ := Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3*Cz+4*Cp+2*Cu, by positivity, ?_⟩
  intro q _ hq chi hchi hsq sigma beta t hs hs2 hb34 hb1 ht hzero
  have hH := modulusHeight_ge_one q t
  have h1 := hpen q chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  change (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
      DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
      Cp*modulusHeight q t-1/(sigma-beta) at h1
  have h2 := hprincipal q ((sigma:ℂ)+(2*t:ℝ)*Complex.I)
    (by simpa using hs) (by simpa using hs2)
  have h2H := modulusHeight_double_le q t
  have hp := real_pole_bound_away_from_zero_sharp q hq hc hs hs2 ht
  have h2' : (-deriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q))
      ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
      DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re ≤
      2*Cu*modulusHeight q t+(sigma-1)*(modulusHeight q t)^2/c^2 := by
    simp only [show ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t by simp,
      DirichletCharacter.LFunctionTrivChar, logDeriv_apply, ← neg_div] at h2
    have hm := mul_le_mul_of_nonneg_left h2H hCu.le
    nlinarith only [h2,hp,hm]
  have hz := hzeta sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  have hz' := (Complex.re_le_norm (-deriv riemannZeta (sigma:ℂ)/riemannZeta (sigma:ℂ))).trans hz
  have hCz' : Cz ≤ Cz*modulusHeight q t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hH hCz
  have hpos := character_log_derivative_positivity chi sigma t hs
  rw [hsq] at hpos
  simp only [div_eq_mul_inv] at hpos h1 h2' hz' ⊢
  nlinarith only [hpos,h1,h2',hz',hCz']

end Ostmann.Dirichlet

end OAI

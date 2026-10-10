import OAI.NumberTheory.Ostmann.Dirichlet.ZetaSeparation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

lemma zeta_log_derivative_regular_split {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv regularZeta s / regularZeta s - 1 / (s - 1) := by
  simp only [regularZeta]
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs]
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  field_simp
  ring

theorem exists_zeta_large_height_strip_bound :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, 3 ≤ |t| → 1 - a / Real.log (|t| + 6) ≤ sigma → sigma ≤ 2 →
        riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖deriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log (|t| + 6)) ^ 2 := by
  classical
  obtain ⟨a, ha, ha100, hsep⟩ := exists_zeta_large_height_zero_separation
  obtain ⟨C, hC, hlocal⟩ := uniform_zeta_local_zero_estimates
  refine ⟨a, ha, ha100, C + C / a + 1, by positivity, ?_⟩
  intro sigma t ht hs hs2
  obtain ⟨hne, hseparate⟩ := hsep sigma t ht hs
  refine ⟨hne, ?_⟩
  obtain ⟨S, hS, _, hmass, hbound⟩ := hlocal t
  let H : ℝ := Real.log (|t| + 6)
  have hH : 1 ≤ H := zeta_height_ge_one t
  have hHp : 0 < H := by linarith
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  have hr : 0 < a / H := by positivity
  have hfrac : a / H ≤ a := by
    apply (div_le_iff₀ hHp).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hH ha.le
  let w : ℂ := ((4 / 5 * (sigma - 2) : ℝ) : ℂ)
  have hw : ‖w‖ ≤ 17 / 20 := by
    change ‖((4 / 5 * (sigma - 2) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    change 1 - a / H ≤ sigma at hs
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs1 : (sigma : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    rw [hi, abs_zero] at ht
    norm_num at ht
  have hwne : regularZeta (zetaDiskPoint t w) ≠ 0 := by
    rw [zetaDiskPoint_ofReal, regularZeta_eq_mul hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hne
  let D : ℂ := deriv regularZeta (zetaDiskPoint t w) / regularZeta (zetaDiskPoint t w)
  let Z : ℂ := ∑ rho ∈ S, (analyticOrderAt (normalizedZeta t) rho).toNat / (w - rho)
  have hterm (rho : ℂ) (hrho : rho ∈ S) :
      ‖((analyticOrderAt (normalizedZeta t) rho).toNat : ℂ) / (w - rho)‖ ≤
        ((analyticOrderAt (normalizedZeta t) rho).toNat : ℝ) / (a / H) := by
    rw [norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr
    exact hseparate rho ((hS rho).mp hrho).1 ((hS rho).mp hrho).2
  have hZ : ‖Z‖ ≤ (C / a) * H ^ 2 := by
    calc
      _ ≤ ∑ rho ∈ S, ‖((analyticOrderAt (normalizedZeta t) rho).toNat : ℂ) / (w - rho)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ rho ∈ S, ((analyticOrderAt (normalizedZeta t) rho).toNat : ℝ) / (a / H) :=
        Finset.sum_le_sum hterm
      _ = (∑ rho ∈ S, ((analyticOrderAt (normalizedZeta t) rho).toNat : ℝ)) / (a / H) := by
        simp only [Finset.sum_div]
      _ ≤ (C * H) / (a / H) := div_le_div_of_nonneg_right hmass hr.le
      _ = _ := by field_simp
  have hb := hbound w hw hwne
  change ‖(5 / 4 : ℂ) * D - Z‖ ≤ C * H at hb
  have hn := norm_add_le ((5 / 4 : ℂ) * D - Z) Z
  rw [sub_add_cancel] at hn
  have hscale : ‖(5 / 4 : ℂ) * D‖ = (5 / 4 : ℝ) * ‖D‖ := by rw [norm_mul]; norm_num
  rw [hscale] at hn
  have hsmall := mul_le_mul_of_nonneg_left (show H ≤ H ^ 2 by nlinarith) hC.le
  have hD : ‖D‖ ≤ (C + C / a) * H ^ 2 := by nlinarith [norm_nonneg D]
  have hnormpole : ‖1 / (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤ 1 := by
    have hh := Complex.abs_im_le_norm (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add, Complex.one_im, sub_zero] at hh
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  rw [zeta_log_derivative_regular_split hs1 hne]
  have he : deriv regularZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) /
      regularZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) = D := by
    dsimp only [D, w]
    rw [zetaDiskPoint_ofReal]
  rw [he]
  exact (norm_sub_le _ _).trans (by change _ ≤ (C + C / a + 1) * H ^ 2; nlinarith)

end Ostmann.Dirichlet

end OAI

import OAI.Combinatorics.ContingencyTables.Dense.DenseLocalGeometry

namespace OAI

/-! # Numerical Poincaré and point mixing for the dense bin sampler -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators

noncomputable section

theorem denseCutConstant_lower (d : ℕ) (hd : 14 ≤ d) :
    1 / (8192 * (d : ℝ) ^ 10) ≤ denseCutConstant d (4 * d ^ 8) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  calc
    _ = (1 / (16 * (d : ℝ))) / (128 * (d : ℝ) * (4 * d ^ 8 : ℕ)) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (binProposal_bounds d hd).2.1 (by positivity)

theorem densePoincareConstant_upper (d : ℕ) (hd : 14 ≤ d) :
    2 / (denseCutConstant d (4 * d ^ 8)) ^ 2 ≤ (d : ℝ) ^ 32 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hk := denseCutConstant_lower d hd
  have hc : (134217728 : ℝ) ≤ (d : ℝ) ^ 12 := by
    exact_mod_cast (show 134217728 ≤ d ^ 12 from
      (by norm_num : 134217728 ≤ 14 ^ 12).trans (Nat.pow_le_pow_left hd 12))
  calc
    _ ≤ 2 / (1 / (8192 * (d : ℝ) ^ 10)) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hk 2
    _ = 134217728 * (d : ℝ) ^ 20 := by field_simp; ring
    _ ≤ (d : ℝ) ^ 12 * (d : ℝ) ^ 20 := by gcongr
    _ = _ := by ring

theorem dense_min_mass_exponential (d q : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    Real.exp (-(d : ℝ) ^ 10) ≤
      (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hk : (0 : ℝ) < 4 * (d : ℝ) ^ 8 := by positivity
  have hl₂ : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlK : Real.log (4 * (d : ℝ) ^ 8) ≤ 4 * (d : ℝ) ^ 8 := by
    have h := Real.log_le_sub_one_of_pos hk
    linarith
  have hq' : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hp : (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 9 := pow_le_pow_right₀ hd₁ (by decide)
  have hsum : 4 * (d : ℝ) ^ 5 * Real.log 2 +
      (q : ℝ) * Real.log (4 * (d : ℝ) ^ 8) ≤ (d : ℝ) ^ 10 := by
    calc
      _ ≤ 4 * (d : ℝ) ^ 5 + (q : ℝ) * (4 * (d : ℝ) ^ 8) := by
        have h1 := mul_le_mul_of_nonneg_left hl₂ (show (0 : ℝ) ≤ 4 * (d : ℝ) ^ 5 by positivity)
        have h2 := mul_le_mul_of_nonneg_left hlK (show (0 : ℝ) ≤ q by positivity)
        linarith
      _ ≤ 4 * (d : ℝ) ^ 9 + d * (4 * (d : ℝ) ^ 8) := by gcongr
      _ = 8 * (d : ℝ) ^ 9 := by ring
      _ ≤ d * (d : ℝ) ^ 9 := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 ≤ d by omega)) (by positivity)
      _ = _ := by ring
  have hpow : (4 * (d : ℝ) ^ 8) ^ q =
      Real.exp ((q : ℝ) * Real.log (4 * (d : ℝ) ^ 8)) := by
    rw [Real.exp_nat_mul, Real.exp_log hk]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hpow, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem dense_mixing_time_arithmetic (d q h : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    Real.exp (-((d ^ 50 * (h + 1) ^ 2 : ℕ) : ℝ) / (d : ℝ) ^ 32) /
        ((2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q) ≤
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h₉ : 8 ≤ d ^ 9 := (show 8 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
  have h₈ : 2 ≤ d ^ 8 := (show 2 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
  have h₁₀ : 8 * d ≤ d ^ 10 := by
    calc
      _ ≤ d ^ 9 * d := Nat.mul_le_mul_right d h₉
      _ = _ := by ring
  have h₁₈ : 2 * d ^ 10 ≤ d ^ 18 := by
    calc
      _ ≤ d ^ 8 * d ^ 10 := Nat.mul_le_mul_right _ h₈
      _ = _ := by ring
  have hbase : (d : ℝ) ^ 10 + 4 * d + 4 ≤ (d : ℝ) ^ 18 := by
    exact_mod_cast (show d ^ 10 + 4 * d + 4 ≤ d ^ 18 by omega)
  have hh : (0 : ℝ) ≤ h := by positivity
  have hquad : (h : ℝ) + 1 ≤ ((h : ℝ) + 1) ^ 2 := by nlinarith
  have htime : (d : ℝ) ^ 10 + 4 * ((h : ℝ) + d) ≤
      (d : ℝ) ^ 18 * ((h : ℝ) + 1) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (h : ℝ) + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hquad (show (0 : ℝ) ≤ (d : ℝ) ^ 18 by positivity)
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) ^ 10 * h by positivity]
  calc
    _ ≤ Real.exp (-((d ^ 50 * (h + 1) ^ 2 : ℕ) : ℝ) / (d : ℝ) ^ 32) /
        Real.exp (-(d : ℝ) ^ 10) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
        (dense_min_mass_exponential d q hd hq)
    _ = Real.exp (-(d : ℝ) ^ 18 * ((h : ℝ) + 1) ^ 2 + (d : ℝ) ^ 10) := by
      rw [← Real.exp_sub]
      congr 1
      push_cast
      field_simp
      ring
    _ ≤ Real.exp (-(4 * ((h : ℝ) + d))) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      nlinarith

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

theorem denseBinChain_polynomial_poincare (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8))) :
    let hK : 1 ≤ 4 * d ^ 8 := denseGridSize_pos d hd
    ∀ f : Grid (I := Fin q) (4 * d ^ 8) → ℝ,
      (denseBinChain R P d hd hfree e hK).variance f ≤
        (d : ℝ) ^ 32 * (denseBinChain R P d hd hfree e hK).energy f := by
  dsimp only
  intro f
  exact (denseBinChain_poincare R P d hd hR hP hRmax hPmax hfree e _ hPL hCheeger f).trans
    (mul_le_mul_of_nonneg_right (densePoincareConstant_upper d hd) (FiniteChain.energy_nonneg _ f))

theorem denseBinChain_point_mixing (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (n : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    let hK : 1 ≤ 4 * d ^ 8 := denseGridSize_pos d hd
    let C := denseBinChain R P d hd hfree e hK
    |C.iterate n (C.pointDensity b) a - 1| ≤
      Real.exp (-(n : ℝ) / (d : ℝ) ^ 32) /
        ((2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q) := by
  dsimp only
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  apply FiniteChain.point_mixing_exp
  · exact one_le_pow₀ hd₁
  · positivity
  · exact denseBinChain_pi_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e
  · exact denseBinChain_polynomial_poincare R P d hd hR hP hRmax hPmax hfree e hPL hCheeger

theorem denseBinChain_relative_mixing (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
    |C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - 1| ≤
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  exact (denseBinChain_point_mixing R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger _ a b).trans (dense_mixing_time_arithmetic d q h hd hq)

/-- Total variation for the actual law, written as its density against the
proved stationary distribution. The pointwise relative bound is stronger
than the manuscript's total-variation conclusion. -/
theorem denseBinChain_total_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (b : Grid (I := Fin q) (4 * d ^ 8)) :
    let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
    (∑ a, |C.π a * C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - C.π a|) / 2 ≤
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
  let δ := (2 : ℝ) ^ (-(4 * ((h : ℝ) + d)))
  have hpoint (a : Grid (I := Fin q) (4 * d ^ 8)) :
      |C.π a * C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - C.π a| ≤ C.π a * δ := by
    calc
      _ = C.π a * |C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - 1| := by
        calc
          _ = |C.π a * (C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - 1)| := by
            congr 1
            ring
          _ = _ := by rw [abs_mul, abs_of_pos (C.positive a)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (denseBinChain_relative_mixing R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
          e hPL hCheeger h a b) (C.positive a).le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  rw [← Finset.sum_mul, C.normalized, one_mul] at hsum
  change _ ≤ δ
  have hδ : 0 ≤ δ := (Real.rpow_pos_of_pos (by norm_num) _).le
  linarith

end

end ContingencyTables.GridBoundary

end OAI

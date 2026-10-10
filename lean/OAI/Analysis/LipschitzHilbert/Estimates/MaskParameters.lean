import OAI.Analysis.LipschitzHilbert.Estimates.TopShape
import OAI.Analysis.LipschitzHilbert.Estimates.MaskComparison

namespace OAI

/-! Choose the mask exponent after the fixed top bounds. Both the
near-region and far-region errors have any prescribed polynomial decay. -/

noncomputable section

namespace LipschitzHilbert

theorem constant_mul_rpow_le (L M a b : ℝ) (hL : 1 ≤ L) (hM : M ≤ L)
    (hab : a+1 ≤ b) : M*L^a ≤ L^b := by
  have hL0 : 0 < L := by linarith
  calc
    _ ≤ L*L^a := mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hL0.le _)
    _ = L^(a+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL hab

theorem top_mask_error_of_exponents (L C H A A1 D x y : ℝ)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hlarge : (4/3:ℝ)*((2:ℝ)^D)^7 ≤ L)
    (hnear : C+H+2 ≤ A) (hfar : C+H+1 ≤ 7*D*(A/2-A1)) :
    |1-topSincMask L A x y| * L^C * (topShape (L^A1) D x y)^7 ≤ L^(-H) := by
  have hL0 : 0 < L := by linarith
  let B := ((2:ℝ)^D)^7
  have hB : 0 ≤ B := by positivity
  have hBL : B ≤ L := by dsimp [B] at *; nlinarith
  apply topSincMask_near_far L A x y (topShape (L^A1) D x y) (L^C) (L^(-H)) ((2:ℝ)^D)
    hL (topShape_nonneg _ _ _ _ (Real.rpow_pos_of_pos hL0 _)) (by positivity) (by positivity)
    (by positivity) (topShape_le _ _ _ _ (Real.rpow_pos_of_pos hL0 _) hD)
  · have hn := constant_mul_rpow_le L ((4/3:ℝ)*B) (C+1-A) (-H) hL hlarge (by linarith)
    convert hn using 1
    dsimp [B]
    rw [show C+1-A = (1-A)+C by ring, Real.rpow_add hL0]
    ring
  · intro hxy
    have hs := topShape_far_seventh L A A1 D x y hL0 hD hxy
    have hp := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hL0.le C)
    have hf := constant_mul_rpow_le L B (C-7*D*(A/2-A1)) (-H) hL hBL (by linarith)
    apply hp.trans
    convert hf using 1
    dsimp [B]
    rw [show C-7*D*(A/2-A1) = C+(-7*D*(A/2-A1)) by ring, Real.rpow_add hL0]
    ring

theorem exists_mask_parameters (C H A1 D : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ x y : ℝ,
      |1-topSincMask L A x y| * L^C * (topShape (L^A1) D x y)^7 ≤ L^(-H) := by
  let A := max (C+H+3) (2*A1+2*(C+H+2)/(7*D))
  let L0 := max 1 ((4/3:ℝ)*((2:ℝ)^D)^7)
  have hA1 : C+H+3 ≤ A := le_max_left _ _
  have hA2 : 2*A1+2*(C+H+2)/(7*D) ≤ A := le_max_right _ _
  have hfar : C+H+1 ≤ 7*D*(A/2-A1) := by
    have heq : (2*(C+H+2)/(7*D))*(7*D) = 2*(C+H+2) := by field_simp
    have hp := mul_le_mul_of_nonneg_right hA2 (show 0 ≤ 7*D by positivity)
    nlinarith
  refine ⟨A,L0,by linarith,le_max_left _ _,?_⟩
  intro L hL x y
  exact top_mask_error_of_exponents L C H A A1 D x y
    ((le_max_left _ _).trans hL) hD.le ((le_max_right _ _).trans hL) (by linarith) hfar

theorem exists_mask_parameters_above (C H A1 D M : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, M < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ x y : ℝ,
      |1-topSincMask L A x y| * L^C * (topShape (L^A1) D x y)^7 ≤ L^(-H) := by
  let A := max (M+1) (max (C+H+3) (2*A1+2*(C+H+2)/(7*D)))
  let L0 := max 1 ((4/3:ℝ)*((2:ℝ)^D)^7)
  have hM : M+1 ≤ A := le_max_left _ _
  have hA1 : C+H+3 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA2 : 2*A1+2*(C+H+2)/(7*D) ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hfar : C+H+1 ≤ 7*D*(A/2-A1) := by
    have heq : (2*(C+H+2)/(7*D))*(7*D) = 2*(C+H+2) := by field_simp
    have hp := mul_le_mul_of_nonneg_right hA2 (show 0 ≤ 7*D by positivity)
    nlinarith
  refine ⟨A,L0,by linarith,by linarith,le_max_left _ _,?_⟩
  intro L hL x y
  exact top_mask_error_of_exponents L C H A A1 D x y
    ((le_max_left _ _).trans hL) hD.le ((le_max_right _ _).trans hL) (by linarith) hfar

end LipschitzHilbert

end

end OAI

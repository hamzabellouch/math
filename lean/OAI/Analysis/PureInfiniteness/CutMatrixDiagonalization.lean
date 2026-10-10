import OAI.Analysis.PureInfiniteness.FiniteMatrixDiagonalization
import OAI.Analysis.JiangSu.TraceCone.Cuntz

namespace OAI

/-! Fixed spectral cuts in finite matrix diagonalization.  The bound depends
on the cut, but not on the two approximation tolerances or matrix size.
This is the form of KR02 Lemmas 5.6 and 5.13 used in spectral localization. -/

noncomputable section
open scoped NNReal

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem finite_matrix_cut_diagonalization (hP : MainGap.PropertyP A)
    (M₀ : ℝ) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ M : Fin n → Fin n → A,
      (∀ i, 0 ≤ M i i) → (∀ i, ‖M i i‖ ≤ M₀) →
      ∀ ε ζ : ℝ, 0 < ε → 0 < ζ → ∃ d : Fin n → A,
      (∀ i, ‖d i‖ ≤ C) ∧
      (∀ i, ‖coefficientMatrix M d i i - MainGap.cut (M i i) δ‖ < ε) ∧
      ∀ i j, i ≠ j → ‖coefficientMatrix M d i j‖ < ζ := by
  classical
  let R : ℝ := (max 0 M₀ + 1) / (δ : ℝ)
  have hR : 0 ≤ R := div_nonneg (by positivity) δ.2
  refine ⟨Real.sqrt R, Real.sqrt_nonneg _, ?_⟩
  intro n M hpos hM ε ζ hε hζ
  let a (i : Fin n) : TraceCone.Positive A := ⟨M i i, hpos i⟩
  choose g hgs hga hgg using fun i => TraceCone.fixedCut_factorization (a i) hδ
  let B (i j : Fin n) : A := g i * M i j * g j
  have hB (i : Fin n) : B i i = (TraceCone.Positive.cut δ (a i)).1 := hga i
  have hBcut (i : Fin n) : B i i = MainGap.cut (M i i) δ := hB i
  have hBp (i : Fin n) : 0 ≤ B i i := by
    rw [hB]
    exact (TraceCone.Positive.cut δ (a i)).2
  have hBn (i : Fin n) : ‖B i i‖ ≤ max 0 M₀ := by
    rw [hB]
    have hc : (TraceCone.Positive.cut δ (a i)).1 ≤ (a i).1 :=
      TraceCone.Positive.cut_le δ (a i)
    exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg hc
      (TraceCone.Positive.cut δ (a i)).2).trans ((hM i).trans (le_max_right _ _))
  obtain ⟨_, _, hfinite⟩ := finite_matrix_diagonalization_uniform hP
    (n := n) (max 0 M₀) (min ε 1) (lt_min hε zero_lt_one)
  obtain ⟨e, _, he, heoff⟩ := hfinite B hBp hBn ζ hζ
  let d (i : Fin n) := g i * e i
  have hentry (i j : Fin n) : coefficientMatrix M d i j = coefficientMatrix B e i j := by
    simp only [coefficientMatrix, d, B, star_mul, hgs, mul_assoc]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i
    have horder : star (d i) * d i ≤ (δ : ℝ)⁻¹ • coefficientMatrix B e i i := by
      have h := star_left_conjugate_le_conjugate (hgg i) (e i)
      simpa only [d, star_mul, hgs, coefficientMatrix, ← hB,
        mul_smul_comm, smul_mul_assoc, mul_assoc] using h
    have hn : ‖d i‖ ^ 2 ≤ (δ : ℝ)⁻¹ * ‖coefficientMatrix B e i i‖ := by
      have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg (d i))
      simpa only [CStarRing.norm_star_mul_self, pow_two, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (show (0 : ℝ) < δ from hδ))] using h
    have heN : ‖coefficientMatrix B e i i‖ ≤ max 0 M₀ + 1 := by
      have h := norm_le_norm_sub_add (coefficientMatrix B e i i) (B i i)
      have ht := (he i).trans_le (min_le_right ε 1)
      have hb := hBn i
      linarith
    have hsq : ‖d i‖ ^ 2 ≤ R := hn.trans (by
      dsimp only [R]
      rw [div_eq_mul_inv, mul_comm (max 0 M₀ + 1)]
      exact mul_le_mul_of_nonneg_left heN (inv_nonneg.mpr δ.2))
    exact (Real.le_sqrt (norm_nonneg _) hR).mpr hsq
  · intro i
    rw [hentry, ← hBcut]
    exact (he i).trans_le (min_le_left ε 1)
  · intro i j hij
    rw [hentry]
    exact heoff i j hij

end WeakPureInfiniteness

end

end OAI

import OAI.Analysis.CStarAlgebra.PureInfiniteness.Diagonalization

namespace OAI

/-! The uniform two-entry step for the finite diagonalization in KR02 Lemma 5.7.
The implementer bound depends on the diagonal tolerance and norm bound, but
not on the off-diagonal entry or its requested error. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem uniform_bounded_pair_diagonalization (hP : MainGap.PropertyP A)
    (M η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : A, 0 ≤ a → 0 ≤ b → ‖a‖ ≤ M → ‖b‖ ≤ M →
      ∀ c : A, ∀ ζ : ℝ, 0 < ζ →
      ∃ s t : A, ‖s‖ ≤ C ∧ ‖t‖ ≤ C ∧
        ‖star s * a * s - a‖ < η ∧ ‖star t * b * t - b‖ < η ∧
        ‖star s * c * t‖ < ζ := by
  let L := max 1 M
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := min (1 / 4 : ℝ) (η / (8 * L))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hδhalf : δ < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : L * (2 * δ + δ) < η := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp (min_le_right (1 / 4) (η / (8 * L)))
    change δ * (8 * L) ≤ η at h
    nlinarith
  refine ⟨max 1 (Real.sqrt δ⁻¹), le_max_left _ _, ?_⟩
  intro a b ha hb han hbn c ζ hζ
  have hscale {x : A} (hx : ‖x‖ ≤ M) : ‖L⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    calc
      _ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left (hx.trans (le_max_right _ _))
        (inv_nonneg.mpr hL.le)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  obtain ⟨s, t, hs, ht, hc, hsn, htn⟩ := MainGap.bounded_diagonalization hP
    (smul_nonneg (inv_nonneg.mpr hL.le) ha)
    (smul_nonneg (inv_nonneg.mpr hL.le) hb)
    (hscale han) (hscale hbn) c hδ hδhalf hδ (by linarith) hζ
  have he (x v : A) : L • (star v * (L⁻¹ • x) * v - L⁻¹ • x) =
      star v * x * v - x := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
      mul_inv_cancel₀ hL.ne', one_smul]
  refine ⟨s, t, hsn.trans (le_max_right _ _), htn.trans (le_max_right _ _), ?_, ?_, hc⟩
  · rw [← he a s, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    exact (mul_lt_mul_of_pos_left hs hL).trans hsmall
  · rw [← he b t, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    exact (mul_lt_mul_of_pos_left ht hL).trans hsmall

end WeakPureInfiniteness

end

end OAI

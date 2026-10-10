import OAI.Analysis.Cotype.ProjectionGenerator
import OAI.Analysis.Cotype.ExponentialIntegral

namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionGenerator_exp_shift {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (s : ℝ) :
    NormedSpace.exp (s • (z • 1 - projectionGenerator P)) =
      Complex.exp (z * (s : ℂ)) • complexProjectionTime P (s : ℂ) := by
  let : NormedAlgebra ℚ (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [complexProjectionTime_eq_exp P hp hc]
  have hsplit : s • (z • 1 - projectionGenerator P) =
      (z * (s : ℂ)) • 1 + (-(s : ℂ)) • projectionGenerator P := by
    ext vector dual
    simp [Complex.real_smul, smul_eq_mul]
    ring
  have hcommute : Commute ((z * (s : ℂ)) •
      (1 : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y))
      ((-(s : ℂ)) • projectionGenerator P) := by
    apply ContinuousLinearMap.ext
    intro vector
    change (z * (s : ℂ)) • ((-(s : ℂ)) • projectionGenerator P vector) =
      (-(s : ℂ)) • projectionGenerator P ((z * (s : ℂ)) • vector)
    rw [(projectionGenerator P).map_smul]
    ext dual
    exact mul_left_comm _ _ _
  rw [hsplit, NormedSpace.exp_add_of_commute hcommute]
  have he := NormedSpace.algebraMap_exp_comm
    (𝕂 := ℂ) (𝔸 := ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) (z * (s : ℂ))
  simp only [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ] at he
  rw [← he]
  ext vector dual
  rfl

def projectionShiftIntegral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) (t : ℝ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  Complex.exp (-(z * (t : ℂ))) •
    exponentialIntegral (z • 1 - projectionGenerator P) t

theorem projectionShiftIntegral_factors {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (t : ℝ) :
    (z • 1 - projectionGenerator P) * projectionShiftIntegral P z t =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z * (t : ℂ))) • 1 ∧
    projectionShiftIntegral P z t * (z • 1 - projectionGenerator P) =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z * (t : ℂ))) • 1 := by
  have he : Complex.exp (-(z * (t : ℂ))) * Complex.exp (z * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hmul_smul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : left * (scalar • right) = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact left.map_smul scalar (right vector)
  have hsmul_mul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : (scalar • left) * right = scalar • (left * right) := by
    ext vector dual
    rfl
  have hsmul_sub (scalar : ℂ)
      (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :
      scalar • (left - right) = scalar • left - scalar • right := by
    ext vector dual
    exact mul_sub scalar _ _
  constructor
  · rw [projectionShiftIntegral, hmul_smul, mul_exponentialIntegral,
      projectionGenerator_exp_shift P hp hc, hsmul_sub, smul_smul, he, one_smul]
  · rw [projectionShiftIntegral, hsmul_mul, exponentialIntegral_mul,
      projectionGenerator_exp_shift P hp hc, hsmul_sub, smul_smul, he, one_smul]

theorem projectionShiftIntegral_norm_le {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ‖projectionShiftIntegral P z t‖ ≤ D*t := by
  rw [projectionShiftIntegral, exponentialIntegral, ← intervalIntegral.integral_smul]
  have he (s : ℝ) :
      Complex.exp (-(z*(t : ℂ))) •
        NormedSpace.exp (s • (z • 1 - projectionGenerator P)) =
      Complex.exp (z * ((s-t : ℝ) : ℂ)) • complexProjectionTime P (s : ℂ) := by
    rw [projectionGenerator_exp_shift P hp hc, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he]
  have hn : ‖∫ s in (0 : ℝ)..t,
      Complex.exp (z * ((s-t : ℝ) : ℂ)) • complexProjectionTime P (s : ℂ)‖ ≤
      D * |t-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    rw [norm_smul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (z.re * (s-t)) * 1 :=
        mul_le_mul_of_nonneg_left (complexProjectionTime_real_norm_le P hP hs0)
          (Real.exp_pos _).le
      _ ≤ D := by simpa using hD s ⟨hs0, hs.2⟩
  simpa [abs_of_nonneg ht] using hn

theorem projectionGenerator_inverse_of_timed_shift
    [Nontrivial (ComplexDualSpace Y)]
    {N : ℕ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖)
    (hpower : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖)
    (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hshift : ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ∃ W : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)ˣ,
      (W : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = z • 1 - projectionGenerator P ∧
      ‖(↑W⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)‖ ≤
        D*t * (powerGapInverseBound N (2/ρ) (C/ρ^N) /
          ‖1-Complex.exp (-(z*(t : ℂ)))‖) := by
  obtain ⟨U, hU, hnU⟩ := exists_complex_shift_inverse_of_power_gap hC hρ hgap
    (complexProjectionTime P (t : ℂ)) (complexProjectionTime_real_norm_le P hP ht)
    (complexProjectionTime_real_power_gap hC P hpower ht)
    (1-Complex.exp (-(z*(t : ℂ)))) hshift
  have hv : (U : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z*(t : ℂ))) • 1 := by
    rw [hU]
    module
  have hf := projectionShiftIntegral_factors P hp hc z t
  obtain ⟨W, hW, hnW⟩ := exists_inverse_of_commuting_factorization
    (z • 1 - projectionGenerator P) (projectionShiftIntegral P z t) U
    (hf.1.trans hv.symm) (hf.2.trans hv.symm)
  refine ⟨W, hW, hnW.trans ?_⟩
  have hD0 : 0 ≤ D := (Real.exp_pos _).le.trans (hD 0 ⟨le_rfl, ht⟩)
  exact mul_le_mul (projectionShiftIntegral_norm_le P hp hc hP z ht hD) hnU
    (norm_nonneg _) (mul_nonneg hD0 ht)

end Cotype

end

end OAI

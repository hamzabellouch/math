import OAI.NumberTheory.CubicMoment.Estimates.TypeIUniform

namespace OAI

/-! Finite level summation of the uniform Type-I estimate. The actual
Gauss sum removes nonsquarefree levels, and the coefficient mass remains
explicit. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticSmoothSum_zero_of_not_squarefree {r : Eisenstein}
    (hr : primary r) (hs : ¬Squarefree r) (W : ℝ → ℂ) (U t : ℝ) :
    metaplecticSmoothSum r W U t = 0 := by
  have hg (u : PrimaryArgument) : gauss (r*u) = 0 :=
    gauss_eq_zero_of_not_squarefree (primary_mul hr u.property)
      (fun h => hs (Squarefree.squarefree_of_dvd (dvd_mul_right _ _) h))
  simp [metaplecticSmoothSum,hg]

lemma dyadic_finite_norm_sum {α : Type*} (S : Finset α) (a : α → ℂ)
    (f : α → ℝ → ℂ) (hf : ∀ i ∈ S, Continuous (f i)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ i ∈ S, ‖a i‖*‖f i t‖)+
     (∫ t in -(2*T)..(-T), ∑ i ∈ S, ‖a i‖*‖f i t‖))/T =
      ∑ i ∈ S, ‖a i‖*((∫ t in T..2*T, ‖f i t‖)+
        (∫ t in -(2*T)..(-T), ‖f i t‖))/T := by
  rw [intervalIntegral.integral_finsetSum,intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    exact (continuous_const.mul (hf i hi).norm).intervalIntegrable _ _
  · intro i hi
    exact (continuous_const.mul (hf i hi).norm).intervalIntegrable _ _

/-- A finite dyad of levels. Only the coefficient L1 mass is needed to
sum the actual original smooth sums. -/
theorem typeI_finite_levels {W : Eisenstein → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) (D : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (S : Finset Eisenstein) (a : Eisenstein → ℂ)
      (R U T A : ℝ), 0 < R → 1 ≤ U → 1 ≤ T →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖a r‖) ≤ A →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖)+
       (∫ t in -(2*T)..(-T), ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W r) U t‖))/T ≤
        (C*U^(1/2+ε)*(2*R)^(1/4+2*ε)*Real.sqrt T+
          E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*A := by
  obtain ⟨C,E,hC,hE,hbound⟩ := uniform_metaplectic_dyadic_height
    hW hF hGrowth hHB hε hεsmall D
  refine ⟨C,E,hC,hE,?_⟩
  intro S a R U T A hR hU hT hS hA
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let B := C*U^(1/2+ε)*(2*R)^(1/4+2*ε)*Real.sqrt T+
    E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticSmoothSum r (W r) U t‖)+
       (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r (W r) U t‖))/T ≤ B := by
    obtain ⟨hprim,hlow,hup⟩ := hS r hr
    by_cases hs : Squarefree r
    · apply (hbound r r hprim hs U hU T hT).trans
      have hp := Real.rpow_le_rpow (norm_nonneg r) hup (by linarith : 0 ≤ 1/4+2*ε)
      have hq := Real.rpow_le_rpow_of_nonpos hR hlow (by norm_num : (-1/6:ℝ) ≤ 0)
      dsimp [B]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Real.rpow_nonneg hUp.le _)))
          (Real.sqrt_nonneg _)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq (mul_nonneg hE (Real.rpow_nonneg hUp.le _)))
          (pow_nonneg hTp.le _)
    · simp only [metaplecticSmoothSum_zero_of_not_squarefree hprim hs,norm_zero,
        intervalIntegral.integral_zero,add_zero,zero_div]
      exact hBn
  rw [dyadic_finite_norm_sum S a (fun r => metaplecticSmoothSum r (W r) U)
    (fun r _ => metaplecticSmoothSum_continuous r (W r) (hW.compact r) hUp)]
  calc
    _ = ∑ r ∈ S, ‖a r‖*(((∫ t in T..2*T, ‖metaplecticSmoothSum r (W r) U t‖)+
        (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r (W r) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ S, ‖a r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖a r‖) := by rw [← Finset.sum_mul,mul_comm]
    _ ≤ B*A := mul_le_mul_of_nonneg_left hA hBn

end CubicFirstMoment

end

end OAI

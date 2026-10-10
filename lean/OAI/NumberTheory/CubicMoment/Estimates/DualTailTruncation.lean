import OAI.NumberTheory.CubicMoment.Estimates.MellinDualTail

namespace OAI

/-! Quantitative truncation at a small power beyond the natural Hecke
length. The cutoff is a numerical inequality, not a duality assumption. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma exists_dual_tail_order {δ : ℝ} (hδ : 0 < δ) (B H : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ 2*B-δ*(m:ℝ) ≤ -H := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 2 ((2*B+H)/δ))
  have hm2 : (2:ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm' : (2*B+H)/δ < m := lt_of_le_of_lt (le_max_right _ _) hm
  have he := (div_lt_iff₀ hδ).mp hm'
  refine ⟨m,?_,by nlinarith⟩
  have : 2 < m := by exact_mod_cast hm2
  omega

lemma dual_tail_scale_bound {δ B H Y A Z J : ℝ} {m : ℕ}
    (hY : 1 ≤ Y) (hA : 0 < A) (hZ : 0 < Z) (hJ : 0 < J)
    (hZB : Z ≤ Y^B) (hJB : J ≤ Y^B)
    (hcut : (A^2*(1+|H|)^2)/(Z*J) ≤ Y^(-δ))
    {R : ℝ} (hm : 2*B-δ*(m:ℝ) ≤ -R) :
    Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|H|)^2)/(Z*J))^m ≤ Y^(-R) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hz : Z^(1/2:ℝ) ≤ Y^(B/2) := by
    calc
      _ ≤ (Y^B)^(1/2:ℝ) := Real.rpow_le_rpow hZ.le hZB (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; congr 1; ring
  have hj : J^(3/2:ℝ) ≤ Y^(3*B/2) := by
    calc
      _ ≤ (Y^B)^(3/2:ℝ) := Real.rpow_le_rpow hJ.le hJB (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; congr 1; ring
  have hc : ((A^2*(1+|H|)^2)/(Z*J))^m ≤ Y^(-δ*(m:ℝ)) := by
    calc
      _ ≤ (Y^(-δ))^m := pow_le_pow_left₀ (by positivity) hcut _
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
  calc
    _ ≤ Y^(B/2)*Y^(3*B/2)*Y^(-δ*(m:ℝ)) := by gcongr
    _ = Y^(2*B-δ*(m:ℝ)) := by rw [← Real.rpow_add hY0,← Real.rpow_add hY0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hm

/-- The omitted far-left tail is smaller than every fixed negative power
once the cutoff exceeds the natural length by `Y^δ`. Only polynomial
upper bounds for the two lengths are used. -/
theorem hecke_dual_tail_arbitrary_power (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J : ℝ),
      1 ≤ Y → 0 < A → 0 < Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      ∀ t : ℝ, (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖∫ τ : ℝ, heckeDualTailIntegrand W χ ε A Z J m t τ‖ ≤ C*Y^(-R) := by
  obtain ⟨m,hm2,hm⟩ := exists_dual_tail_order hδ B R
  obtain ⟨C,hC,hbound⟩ := hecke_dual_tail_integral_bound W hW hpos hsm hm2
  refine ⟨m,C,hm2,hC,?_⟩
  intro χ hχ ε hε Y A Z J hY hA hZ hJ hZB hJB t hcut
  calc
    _ ≤ C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m :=
      hbound χ hχ ε hε A Z J hA hZ hJ t
    _ = C*(Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_tail_scale_bound hY hA hZ hJ hZB hJB hcut hm) hC

end CubicFirstMoment

end

end OAI

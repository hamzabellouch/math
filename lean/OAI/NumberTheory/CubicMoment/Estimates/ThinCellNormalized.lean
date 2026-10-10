import OAI.NumberTheory.CubicMoment.Estimates.ThinCellPowerScale

namespace OAI

/-! The thin-cell estimate at the Patterson dispersion scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma thinCell_outer_scale {Z A γ : ℝ} (hZ : 0 < Z) (hA : 0 < A)
    (hupper : A ≤ Z^(2+γ)) :
    A/Z^γ ≤ A^(2/3:ℝ)*Z^(2/3-2*γ/3) := by
  have hp := Real.rpow_le_rpow hA.le hupper (by norm_num : (0:ℝ) ≤ 1/3)
  rw [←Real.rpow_mul hZ.le] at hp
  calc
    A/Z^γ = (A^(2/3:ℝ)*A^(1/3:ℝ))/Z^γ := by
      rw [←Real.rpow_add hA]
      norm_num
    _ ≤ (A^(2/3:ℝ)*Z^((2+γ)*(1/3:ℝ)))/Z^γ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
        (Real.rpow_nonneg hZ.le _)
    _ = _ := by
      rw [mul_div_assoc,←Real.rpow_sub hZ]
      congr 2
      ring

theorem thinCell_bilinear_normalized
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (γ K : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(2-1/80000:ℝ) ≤ A → A ≤ Z^(2+γ) → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ 1+1/(4*Z^γ) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*Z^γ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-2*γ/3)*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨γ,K,hγ,hK,hbound⟩ := thinCell_bilinear_power_saving hMV hC hHuxley
  refine ⟨γ,K,hγ,hK,?_⟩
  intro P S α β Z A T u hZ hA hupper hT hP hS
  have hZp : 0 < Z := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  apply (hbound P S α β Z A T u hZ hA hT hP hS).trans
  have hc := mul_le_mul_of_nonneg_left (thinCell_outer_scale hZp hAp hupper) hK.le
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq
  ring

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Estimates.ThinCellBilinear

namespace OAI

/-! A concrete positive cell exponent absorbs the finite derivative cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def thinCellExponent (d : ℕ) : ℝ := 1/(240000*((d:ℝ)+1))

lemma thinCellExponent_pos (d : ℕ) : 0 < thinCellExponent d := by
  unfold thinCellExponent
  positivity

lemma thinCellScale_power (d : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    (Z^(thinCellExponent d))^(d+1) = Z^(1/240000:ℝ) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  unfold thinCellExponent
  push_cast
  field_simp

lemma thinCell_error_absorbed (d : ℕ) {Z A : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(2-1/80000:ℝ) ≤ A) :
    (Z^(thinCellExponent d))^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ) ≤
      A/(Z^(thinCellExponent d)) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hJp : 0 < Z^(thinCellExponent d) := Real.rpow_pos_of_pos hZp _
  have hac := Real.rpow_le_rpow (Real.rpow_nonneg hZp.le (2-1/80000:ℝ)) hA
    (by norm_num : (0:ℝ) ≤ 1/3)
  rw [←Real.rpow_mul hZp.le] at hac
  have hp : (Z^(thinCellExponent d))^(d+1)*Z^(2/3-1/80000:ℝ) ≤ A^(1/3:ℝ) := by
    rw [thinCellScale_power d hZp,←Real.rpow_add hZp]
    exact (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)).trans hac
  apply (le_div_iff₀ hJp).mpr
  calc
    _ = A^(2/3:ℝ)*((Z^(thinCellExponent d))^(d+1)*Z^(2/3-1/80000:ℝ)) := by
      rw [pow_succ]
      ring
    _ ≤ A^(2/3:ℝ)*A^(1/3:ℝ) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = A := by rw [←Real.rpow_add hAp]; norm_num

theorem thinCell_bilinear_power_saving
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (γ K : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(2-1/80000:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ 1+1/(4*Z^γ) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*Z^γ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      K*(A/Z^γ)*(∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hbound⟩ := thinCell_bilinear_height_square hMV hC hHuxley
  refine ⟨thinCellExponent d,2*K,thinCellExponent_pos d,by positivity,?_⟩
  intro P S α β Z A T u hZ hA hT hP hS
  have hZ1 : 1 ≤ Z := by linarith
  have hJA : 1 ≤ Z^(thinCellExponent d) := Real.one_le_rpow hZ1 (thinCellExponent_pos d).le
  have hA0 : Z^(3/2:ℝ) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : (3/2:ℝ) ≤ 2-1/80000)).trans hA
  have hb := hbound (Z^(thinCellExponent d)) hJA P S α β Z A T u hZ hA0 hT hP hS
  have hp := thinCell_error_absorbed d hZ1 hA
  apply hb.trans
  have hcoef : K*(A/Z^(thinCellExponent d)+
      (Z^(thinCellExponent d))^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)) ≤
        2*K*(A/Z^(thinCellExponent d)) := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CubicFirstMoment

end

end OAI

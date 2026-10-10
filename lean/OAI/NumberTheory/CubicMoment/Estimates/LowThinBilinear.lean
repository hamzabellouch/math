import OAI.NumberTheory.CubicMoment.Estimates.LowThinCell
import OAI.NumberTheory.CubicMoment.Estimates.HeightSquareRoot

namespace OAI

/-! The thin diagonal keeps the actual coefficient energy, while only
the off-diagonal remainder uses the uniform coefficient bound. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem low_thinCell_bilinear_height_square
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 1 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1+1/(4*J) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*J)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      K*((A/J)*(∑ b ∈ S, ‖β b‖^2)+
        J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j)*(∑ a ∈ P, ‖α a‖^2) := by
  obtain ⟨d,hfamily⟩ := low_thinCell_variance_height hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K,Ct,hK,?_⟩
  intro J hJ P S α β Z A T M u hZ hA hT hM hP hS hβ
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by nlinarith : 0 < Z) _).trans_le hA
  have hZ1 : 1 ≤ Z := by nlinarith
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  have hb := height_bilinear_full_variance_bound_sq P S α β u
    (fun a ha => (hP a ha).1) (fun b hb => (hS b hb).1)
    (thinCellCutoff J) (thinCellCutoff_nonneg J)
    (thinCellCutoff_compact J hJp.ne') (thinCellCutoff_smooth J hJp.ne') hAp hTp
    (fun a ha => by rw [thinCellCutoff_one hJp (hP a ha).2])
  exact hb.trans ((mul_le_mul_of_nonneg_left
    (hbound J hJ S β Z A T M u hZ hA hT hM hS hβ)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq (by ring))

end CubicFirstMoment

end

end OAI

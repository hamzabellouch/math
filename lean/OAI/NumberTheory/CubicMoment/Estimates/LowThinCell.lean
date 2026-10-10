import OAI.NumberTheory.CubicMoment.Estimates.LowShrinkingVariance
import OAI.NumberTheory.CubicMoment.Estimates.ThinCellBilinear

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem low_thinCell_variance_height
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ) (_hJ : 1 ≤ J) (S : Finset Eisenstein)
        (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t)
        (fun x => (thinCellCutoff J x : ℂ)) A‖) T ≤
        K*((A/J)*(∑ b ∈ S, ‖β b‖^2)+
          J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j) := by
  obtain ⟨d,hfamily⟩ := low_shrinking_variance_remainder hpnt hMV hC hHuxley
    thinBaseSchwartz thinBaseSchwartz_compact
  let D := 2*Real.pi/(9*Real.sqrt 3)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K+2*D,Ct,by positivity,?_⟩
  intro J hJ S β Z A T M u hZ hA hT hM hS hβ
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL _).trans_le hT
  let V := fun x => (thinCellCutoff J x : ℂ)
  let Q := varianceZeroMode S β V A
  let R := fun t => smoothedDispersionVariance S β (u+t) V A-Q
  have hshift : |1+1/(2*J)| ≤ 2 := by
    rw [abs_of_pos (by positivity)]
    have hh : 1/(2*J) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hb := hbound J (1+1/(2*J)) hJ hshift S β Z A T M u hZ hA hT hM hS hβ
  rw [←thinCellCutoff_eq_affine J hJp.ne'] at hb
  have hz := thin_varianceZeroMode_bound S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) β V hAp.le hJp
    (thinCellCutoff_norm J) (thinCellCutoff_support hJp)
  have hcont : Continuous (fun t => smoothedDispersionVariance S β (u+t) V A) :=
    (continuous_smoothedDispersionVariance S (fun b hb => (hS b hb).1) β V
      (thinCellCutoff_compact J hJp.ne') (thinCellCutoff_smooth J hJp.ne') hAp).comp
      (continuous_const.add continuous_id)
  have hRc : Continuous R := hcont.sub continuous_const
  have hm := dyadicHeightMean_mono hcont.norm (hRc.norm.add continuous_const) hTp
    (fun t _ => show ‖smoothedDispersionVariance S β (u+t) V A‖ ≤ ‖R t‖+‖Q‖ from
      norm_le_norm_sub_add _ _)
  change dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
    dyadicHeightMean (fun t => ‖R t‖+‖Q‖) T at hm
  rw [dyadicHeightMean_add hRc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  apply hm.trans
  have hmain := add_le_add hb (mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ) ≤ 2))
  apply hmain.trans
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : 0 ≤ J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by positivity
  have hAJ : 0 ≤ A/J := by positivity
  let E := (A/J)*(∑ b ∈ S, ‖β b‖^2)
  let X := J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j
  have hmissing : 0 ≤ K*E+2*D*X :=
    add_nonneg (mul_nonneg hK.le (mul_nonneg hAJ hE))
      (mul_nonneg (mul_nonneg (by norm_num) hD.le) hX)
  calc
    _ = K*X+2*D*E := by dsimp [X,E,D]; ring
    _ ≤ (K*X+2*D*E)+(K*E+2*D*X) := le_add_of_nonneg_right hmissing
    _ = _ := by dsimp [X,E]; ring

end CubicFirstMoment

end

end OAI

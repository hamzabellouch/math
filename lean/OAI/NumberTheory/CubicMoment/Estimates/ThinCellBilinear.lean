import OAI.NumberTheory.CubicMoment.Estimates.ThinCellCutoff
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinear

namespace OAI

/-! The actual Gauss bilinear form localized to a thin norm cell. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem thinCell_variance_height
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ) (_hJ : 1 ≤ J) (S : Finset Eisenstein)
        (β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t)
        (fun x => (thinCellCutoff J x : ℂ)) A‖) T ≤
        K*(A/J+J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨d,K,hK,hbound⟩ := smallB_shrinking_variance_remainder hMV hC hHuxley
    thinBaseSchwartz thinBaseSchwartz_compact
  let D := 2*Real.pi/(9*Real.sqrt 3)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨d,K+2*D,by positivity,?_⟩
  intro J hJ S β Z A T u hZ hA hT hS
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  have hTp : 0 < T := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hT
  let V := fun x => (thinCellCutoff J x : ℂ)
  let Q := varianceZeroMode S β V A
  let R := fun t => smoothedDispersionVariance S β (u+t) V A-Q
  have hshift : |1+1/(2*J)| ≤ 2 := by
    rw [abs_of_pos (by positivity)]
    have hh : 1/(2*J) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hb := hbound J (1+1/(2*J)) hJ hshift S β Z A T u hZ hA hT hS
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
  have hX : 0 ≤ J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ) := by positivity
  have hAJ : 0 ≤ A/J := by positivity
  have he1 := mul_nonneg hK.le (mul_nonneg hAJ hE)
  have he2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hD.le)
    (mul_nonneg hX hE)
  dsimp only [D] at he2 ⊢
  nlinarith only [he1,he2]

theorem thinCell_bilinear_height_square
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ) (_hJ : 1 ≤ J) (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ 1+1/(4*J) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*J)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
      K*(A/J+J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))*
        (∑ a ∈ P, ‖α a‖^2)*(∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hbound⟩ := thinCell_variance_height hMV hC hHuxley
  refine ⟨d,K,hK,?_⟩
  intro J hJ P S α β Z A T u hZ hA hT hP hS
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  have hTp : 0 < T := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hT
  have hb := height_bilinear_full_variance_bound_sq P S α β u
    (fun a ha => (hP a ha).1) (fun b hb => (hS b hb).1)
    (thinCellCutoff J) (thinCellCutoff_nonneg J)
    (thinCellCutoff_compact J hJp.ne') (thinCellCutoff_smooth J hJp.ne') hAp hTp
    (fun a ha => by rw [thinCellCutoff_one hJp (hP a ha).2])
  exact hb.trans ((mul_le_mul_of_nonneg_left (hbound J hJ S β Z A T u hZ hA hT hS)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq (by ring))

end CubicFirstMoment

end

end OAI

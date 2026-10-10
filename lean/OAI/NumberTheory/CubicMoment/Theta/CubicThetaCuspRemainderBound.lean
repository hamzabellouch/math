import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRemainder

namespace OAI

/-! Absolute lattice summation gives a uniform bound for the literal
Eisenstein-minus-incoming remainder in every integral cusp. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspRemainderConstant (s : ℂ) (R : ℝ) : ℝ :=
  2*(3+2*R)^2*(∑' c : Eisenstein, (norm c)^(-(s.re-2)))*
    (∑' d : Eisenstein, (1+norm d)^(-2:ℝ))

lemma cubicThetaCuspRemainderConstant_nonneg (s : ℂ) (R : ℝ) :
    0≤cubicThetaCuspRemainderConstant s R := by
  unfold cubicThetaCuspRemainderConstant
  apply mul_nonneg
  · apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    exact tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _)
  · exact tsum_nonneg (fun d => Real.rpow_nonneg (by linarith [norm_nonneg d]) _)

theorem cubicThetaArithmeticRemainder_cusp_bound
    (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein) (z : ℂ)
    {v R : ℝ} (hv : 2≤v) (hz : Complex.normSq z≤R) {s : ℂ} (hs : 3<s.re) :
    ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤
      cubicThetaCuspRemainderConstant s R*v^(4-s.re) := by
  have hv0 : 0<v := by linarith
  let F : Eisenstein × Eisenstein → ℝ := fun cd =>
    (norm cd.1)^(-(s.re-2))*(1+norm cd.2)^(-2:ℝ)
  have hc := summable_eisenstein_norm_rpow (show 1<s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  have hF : Summable F := summable_mul_of_summable_norm hc.norm hd.norm
  have hF0 (cd : Eisenstein × Eisenstein) : 0≤F cd :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)
  let j : CubicThetaBottomRow → Eisenstein × Eisenstein :=
    fun r => ((cubicThetaCuspRow δ r).c,(cubicThetaCuspRow δ r).d)
  have hj : Function.Injective j := by
    intro r t h
    exact cubicThetaCuspRow_injective δ
      (CubicThetaPrimitiveRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let K : ℝ := 2*(3+2*R)^2*v^(4-s.re)
  have hK : 0≤K := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (Real.rpow_nonneg hv0.le _)
  have hM : Summable (fun cd => K*F cd) := hF.mul_left K
  have hmr : Summable (fun r => K*F (j r)) := hM.comp_injective hj
  have hb (r : CubicThetaBottomRow) :
      ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤K*F (j r) := by
    simpa only [K,F,j,mul_assoc] using cubicThetaRemainderRow_cusp_bound δ r z hv hz
      (show 2 ≤ s.re by linarith)
  have hsum := cubicThetaRemainderRow_summable (cubicThetaMobius_height_pos (p := (z,v)) (cubicThetaFullComplex δ) hv0)
    (show 2<s.re by linarith)
  rw [cubicThetaArithmeticRemainder_eq_sum (cubicThetaMobius_height_pos (p := (z,v)) (cubicThetaFullComplex δ) hv0)
    (show 2<s.re by linarith)]
  calc
    _ ≤ ∑' r, ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' r, K*F (j r) := Summable.tsum_le_tsum hb hsum.norm hmr
    _ ≤ ∑' cd, K*F cd := tsum_comp_le_tsum_of_inj hM (fun cd => mul_nonneg hK (hF0 cd)) hj
    _ = K*((∑' c : Eisenstein, (norm c)^(-(s.re-2)))*
        (∑' d : Eisenstein, (1+norm d)^(-2:ℝ))) := by
      rw [tsum_mul_left,← hc.tsum_mul_tsum hd hF]
    _ = _ := by unfold K cubicThetaCuspRemainderConstant; ring

end CubicFirstMoment

end

end OAI

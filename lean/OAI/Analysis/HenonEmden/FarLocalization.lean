import OAI.Analysis.HenonEmden.FarInteraction

namespace OAI

section FarLocalization

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

def farLocalConstant (n : ℕ) : ℝ := 2*3^(N n)+2*derivativeConstant n

lemma norm_X_bound {n : ℕ} (x : Space n) : ‖X n x‖ ≤ 2*eta n x := by
  by_cases hx : ‖x‖ ≤ 2
  · rw [X,norm_smul,Real.norm_eq_abs,abs_of_nonneg (eta_nonneg n x)]
    nlinarith [eta_nonneg n x]
  · simp only [X,eta_eq_zero (le_of_not_ge hx),zero_smul,norm_zero,mul_zero,le_refl]

lemma fluxFactor_bound {n : ℕ} (x y : Space n) :
    |fluxFactor n (x,y)| ≤ 2*(eta n x+eta n y)/‖x-y‖ := by
  by_cases hxy : x=y
  · subst y
    simp only [fluxFactor,sub_self,inner_zero_left,zero_div,abs_zero,norm_zero,div_zero,le_refl]
  have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [fluxFactor,abs_div,abs_of_nonneg (sq_nonneg ‖x-y‖),div_le_div_iff₀ (sq_pos_of_pos hL) hL]
  have hh := (abs_real_inner_le_norm (x-y) (X n x-X n y)).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
  have hm := add_le_add (norm_X_bound x) (norm_X_bound y)
  have hh' := mul_le_mul_of_nonneg_left hm (norm_nonneg (x-y))
  nlinarith [mul_le_mul_of_nonneg_right (hh.trans hh') (norm_nonneg (x-y))]

lemma localError_rough {n : ℕ} (x y : Space n) :
    localError (x,y) ≤ (2*eta n x/‖x-y‖+2*eta n x+w n x)+
      (2*eta n y/‖x-y‖+2*eta n y+w n y) := by
  have hηx := eta_nonneg n x
  have hηy := eta_nonneg n y
  have hwx := w_nonneg n x
  have hwy := w_nonneg n y
  have hD := radialFactor_bounds (x,y)
  have hh : |fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y)| ≤ |fluxFactor n (x,y)|+eta n x+w n x := by
    have hs : |fluxFactor n (x,y)-eta n x| ≤ |fluxFactor n (x,y)|+eta n x := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hηx] using abs_sub_le (fluxFactor n (x,y)) 0 (eta n x)
    have hw : |w n x*radialFactor (x,y)| ≤ w n x := by
      rw [abs_of_nonneg (mul_nonneg hwx hD.1)]
      exact mul_le_of_le_one_right hwx hD.2
    exact (abs_add_le _ _).trans (by linarith)
  have he : |eta n x-eta n y| ≤ eta n x+eta n y := by
    simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hηx,abs_of_nonneg hηy] using abs_sub_le (eta n x) 0 (eta n y)
  have hf := fluxFactor_bound x y
  unfold localError
  rw [mul_add,add_div] at hf
  linarith

lemma endpoint_far_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x y : Space n} (hne : x ≠ y)
    (hfar : 0 < d x → δ*d x^(m n) ≤ ‖x-y‖) :
    2*eta n x/‖x-y‖+2*eta n x+w n x ≤ farLocalConstant n*
      (farWeight δ (N n-1:ℕ) (x,y)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (x,y)) := by
  have hd := d_nonneg x
  have hN := N_ge_two n
  have hC : 0 ≤ derivativeConstant n := (constants_nonneg n).1
  by_cases hx : 0 < d x
  · have hf := hfar hx
    simp only [farWeight,ite_eq_left (show 0 < d x ∧ δ*d x^(m n) ≤ ‖x-y‖ from ⟨hx,hf⟩),Real.rpow_natCast]
    have hη := (eta_gap_bounds n x).2
    have hw : w n x ≤ 2*derivativeConstant n*d x^(N n-1) := by
      convert wProfile_bound n (norm_nonneg x) using 1
      · exact w_eq_profile n x
      · dsimp [derivativeConstant,d]; ring
    have hpow : d x^(N n) ≤ d x^(N n-1) := pow_le_pow_of_le_one hd (d_le_one x) (by omega)
    have hη' : eta n x ≤ 3^(N n)*d x^(N n-1) := hη.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hηL : 2*eta n x/‖x-y‖ ≤ 2*3^(N n)*δ⁻¹*d x^((N n:ℝ)-(m n:ℝ)) := by
      have hh := div_le_div₀ (by positivity : 0 ≤ 2*(3^(N n)*d x^(N n))) (show 2*eta n x ≤ 2*(3^(N n)*d x^(N n)) by linarith)
        (mul_pos hδ (pow_pos hx _)) hf
      apply hh.trans_eq
      rw [Real.rpow_sub hx,Real.rpow_natCast,Real.rpow_natCast]
      field_simp
    have hp0 : 0 ≤ δ⁻¹*d x^((N n:ℝ)-(m n:ℝ)) := mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hd _)
    unfold farLocalConstant
    have hm := mul_nonneg hC hp0
    nlinarith [hηL,hw,hη']
  · have hx2 : 2 ≤ ‖x‖ := not_lt.mp (fun hh => hx ((d_pos_iff x).mpr hh))
    simp only [eta_eq_zero hx2,w_outer n hx2,mul_zero,zero_div,farWeight,hx,false_and,
      ite_false,add_zero,le_refl]

lemma far_pair_endpoint {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {x y : Space n}
    (hf : ¬(0 < pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y)^(m n))) :
    (0 < d x → δ*d x^(m n) ≤ ‖x-y‖) ∧ (0 < d y → δ*d y^(m n) ≤ ‖x-y‖) := by
  have hsx : d x ≤ pairGap (x,y) := le_max_left _ _
  have hsy : d y ≤ pairGap (x,y) := le_max_right _ _
  constructor
  · intro hx
    have hs := hx.trans_le hsx
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg x) hsx _) hδ).trans
      (le_of_lt (not_le.mp (fun hL => hf ⟨hs,hL⟩)))
  · intro hy
    have hs := hy.trans_le hsy
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg y) hsy _) hδ).trans
      (le_of_lt (not_le.mp (fun hL => hf ⟨hs,hL⟩)))

lemma localError_far {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x y : Space n} (hne : x ≠ y)
    (hf : ¬(0 < pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y)^(m n))) :
    localError (x,y) ≤ farLocalConstant n*
      (farWeight δ (N n-1:ℕ) (x,y)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (x,y)+
      farWeight δ (N n-1:ℕ) (y,x)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (y,x)) := by
  obtain ⟨hx,hy⟩ := far_pair_endpoint hδ.le hf
  have hh := endpoint_far_bound hδ hne hx
  have hh' := endpoint_far_bound hδ hne.symm (fun hy' => by simpa only [norm_sub_rev y x] using hy hy')
  rw [norm_sub_rev y x] at hh'
  exact (localError_rough x y).trans ((add_le_add hh hh').trans_eq (by ring))

end HenonLaneEmden
end
end FarLocalization

end OAI

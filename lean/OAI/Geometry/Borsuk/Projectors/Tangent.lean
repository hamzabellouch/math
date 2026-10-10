import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Finset
open scoped RealInnerProductSpace
section Tangent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def tangentPart (x v : E) : E := v - ⟪x,v⟫ • x

lemma tangentPart_add (x u v : E) : tangentPart x (u+v) = tangentPart x u + tangentPart x v := by
  simp only [tangentPart,inner_add_right,add_smul]
  abel

lemma tangentPart_smul (x v : E) (t : ℝ) : tangentPart x (t • v) = t • tangentPart x v := by
  simp only [tangentPart,inner_smul_right,smul_sub,smul_smul]

lemma tangentPart_self {x : E} (hx : ‖x‖ = 1) : tangentPart x x = 0 := by
  simp [tangentPart,hx]

lemma tangentPart_sq {x : E} (hx : ‖x‖ = 1) (v : E) :
    ‖tangentPart x v‖ ^ 2 = ‖v‖ ^ 2 - ⟪x,v⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [tangentPart,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,sq_abs,hx,mul_one]
  rw [real_inner_comm v x]
  ring

lemma tangentPart_norm_le {x : E} (hx : ‖x‖ = 1) (v : E) : ‖tangentPart x v‖ ≤ ‖v‖ := by
  have hh := tangentPart_sq hx v
  nlinarith [sq_nonneg ⟪x,v⟫,norm_nonneg (tangentPart x v),norm_nonneg v]

lemma dist_le_two_tangent {x z : E} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hpos : 0 ≤ ⟪x,z⟫) : ‖z-x‖ ≤ 2*‖tangentPart x z‖ := by
  have ht := tangentPart_sq hx z
  have hs : ‖z-x‖ ^ 2 = 2 - 2*⟪x,z⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq,hx,hz,one_pow]
    rw [real_inner_comm z x]
    ring
  have hc : ⟪x,z⟫ ≤ 1 := by simpa [hx,hz] using real_inner_le_norm x z
  have hp : 0 ≤ (1-⟪x,z⟫)*⟪x,z⟫ := mul_nonneg (sub_nonneg.mpr hc) hpos
  rw [hz] at ht
  nlinarith [norm_nonneg (z-x),norm_nonneg (tangentPart x z)]

lemma tangentPart_sub (x u v : E) : tangentPart x (u-v) = tangentPart x u - tangentPart x v := by
  rw [sub_eq_add_neg,tangentPart_add]
  have hh := tangentPart_smul x v (-1)
  simpa only [neg_one_smul,sub_eq_add_neg] using congrArg (fun z => tangentPart x u + z) hh

lemma tangentPart_zero (x : E) : tangentPart x 0 = 0 := by simp [tangentPart]

lemma tangentPart_equiv_bound (A : E ≃L[ℝ] E) {x y : E} (hx : ‖x‖ = 1)
    (hA : A x = y) (z : E) :
    ‖tangentPart x z‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖tangentPart y (A z)‖ := by
  have he : tangentPart x (A.symm (tangentPart y (A z))) = tangentPart x z := by
    simp only [tangentPart,map_sub,map_smul,A.symm_apply_apply,← hA]
    simp only [inner_sub_right,real_inner_smul_right]
    have hh : ⟪x,x⟫ = 1 := by simp [hx]
    rw [hh]
    module
  rw [← he]
  exact (tangentPart_norm_le hx _).trans (A.symm.toContinuousLinearMap.le_opNorm _)

lemma spherical_local_linear_interpolation
    (A : E ≃L[ℝ] E) {H : E → E} {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hA : A x = y) (hH : H x = y)
    (hd : HasFDerivAt H A.toContinuousLinearMap x) :
    ∃ δ > 0, ∀ z, dist z x < δ → ‖z‖ = 1 → ∀ t ∈ Set.Icc (0:ℝ) 1,
      ((1-t) • H z + t • A z ≠ 0) ∧
      (tangentPart y ((1-t) • H z + t • A z) = 0 ↔ z = x) := by
  let K : ℝ := ‖A.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hε : 0 < (4*K)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hK)
  have herr := hd.isLittleO.def hε
  have hcontH : ContinuousAt (fun z => ⟪y,H z⟫) x := continuousAt_const.inner hd.continuousAt
  have hcontA : ContinuousAt (fun z => ⟪y,A z⟫) x := continuousAt_const.inner A.continuous.continuousAt
  have hcontx : ContinuousAt (fun z : E => ⟪x,z⟫) x := continuousAt_const.inner continuousAt_id
  have hhH : ∀ᶠ z in nhds x, 0 < ⟪y,H z⟫ :=
    hcontH (isOpen_Ioi.mem_nhds (by simp [hH,hy]))
  have hhA : ∀ᶠ z in nhds x, 0 < ⟪y,A z⟫ :=
    hcontA (isOpen_Ioi.mem_nhds (by simp [hA,hy]))
  have hhp : ∀ᶠ z in nhds x, 0 < ⟪x,z⟫ :=
    hcontx (isOpen_Ioi.mem_nhds (by simp [hx]))
  have hh : ∀ᶠ z in nhds x,
      ‖H z - A z‖ ≤ (4*K)⁻¹ * ‖z-x‖ ∧ 0 < ⟪y,H z⟫ ∧ 0 < ⟪y,A z⟫ ∧ 0 < ⟪x,z⟫ := by
    filter_upwards [herr,hhH,hhA,hhp] with z he h1 h2 h3
    refine ⟨?_,h1,h2,h3⟩
    have hei : H z - H x - A.toContinuousLinearMap (z-x) = H z - A z := by
      change H z - H x - A (z-x) = H z - A z
      rw [map_sub,hH,hA]
      abel
    rwa [hei] at he
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨δ,hδ,?_⟩
  intro z hz hzn t ht
  obtain ⟨he,h1,h2,h3⟩ := hball hz
  have htp : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hpos : 0 < ⟪y,(1-t) • H z + t • A z⟫ := by
    simp only [inner_add_right,real_inner_smul_right]
    by_cases ht0 : t = 0
    · simpa [ht0] using h1
    · exact add_pos_of_nonneg_of_pos (mul_nonneg htp h1.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) h2)
  refine ⟨by intro hz0; simp [hz0] at hpos,?_⟩
  constructor
  · intro htan
    by_contra hzx
    have hdpos : 0 < ‖z-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    have hbound := (dist_le_two_tangent hx hzn h3.le).trans
      (mul_le_mul_of_nonneg_left (tangentPart_equiv_bound A hx hA z) (by norm_num : (0:ℝ) ≤ 2))
    have herrTan : ‖tangentPart y (H z) - tangentPart y (A z)‖ ≤ (4*K)⁻¹ * ‖z-x‖ := by
      rw [← tangentPart_sub]
      exact (tangentPart_norm_le hy _).trans he
    have heTan : tangentPart y (A z) = -(1-t) • (tangentPart y (H z) - tangentPart y (A z)) := by
      rw [tangentPart_add,tangentPart_smul,tangentPart_smul] at htan
      have he0 : tangentPart y (A z) + (1-t) • (tangentPart y (H z) - tangentPart y (A z)) = 0 := by
        calc
          _ = (1-t) • tangentPart y (H z) + t • tangentPart y (A z) := by module
          _ = 0 := htan
      simpa only [neg_smul] using (eq_neg_iff_add_eq_zero.mpr he0)
    have hnorm : ‖tangentPart y (A z)‖ ≤ (4*K)⁻¹ * ‖z-x‖ := by
      rw [heTan,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg htp]
      exact (mul_le_mul_of_nonneg_left herrTan htp).trans
        (mul_le_of_le_one_left (mul_nonneg hε.le (norm_nonneg _)) (by linarith [ht.1]))
    have heK : 2*K*((4*K)⁻¹ * ‖z-x‖) = ‖z-x‖ / 2 := by field_simp; ring
    have hsmall : ‖z-x‖ ≤ ‖z-x‖ / 2 := by
      calc
        ‖z-x‖ ≤ 2 * (‖A.symm.toContinuousLinearMap‖ * ‖tangentPart y (A z)‖) := hbound
        _ ≤ 2 * (K * ‖tangentPart y (A z)‖) := by gcongr; dsimp [K]; linarith
        _ ≤ 2 * (K * ((4*K)⁻¹ * ‖z-x‖)) := by gcongr
        _ = ‖z-x‖ / 2 := by simpa only [mul_assoc] using heK
    linarith
  · rintro rfl
    rw [hH,hA,← add_smul]
    simp [tangentPart_self hy]

end Tangent
end BorsukNine

end OAI

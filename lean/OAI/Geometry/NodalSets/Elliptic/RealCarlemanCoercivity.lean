import OAI.Geometry.NodalSets.Elliptic.RealTransportQuadratic
import OAI.Geometry.NodalSets.Elliptic.RealWeightedShift

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_carleman_coercivity (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (a b C s t : ℝ) (hC : 0 ≤ C) (ht : 1 ≤ t) (hlarge : C+s^2 ≤ b*t)
    (hquad : ∀ x ∈ tsupport v, ∀ xi : Yau.Jets.Coord,
      a*(∑ i, (xi i)^2) ≤ realTransportQuadratic B V x xi + s*coordMatrixForm (B x) xi xi)
    (hweight : ∀ x ∈ tsupport v, b ≤ Yau.pairing q V x-s*q x)
    (herror : ∀ x ∈ tsupport v,
      realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C) :
    2*a*t*(∫ x, gamma x*realGradientSquare v x) + b*t^3*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x-
        t*Yau.weightedSkewTransport gamma V v x)^2) := by
  have hgn (x) := (hgp x).ne'
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hvsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    first | rfl | (ext point; simp [pow_two])
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiq : Integrable (fun x ↦ gamma x*q x*v x^2) :=
    ((hg.mul hq).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiW : Integrable (fun x ↦ gamma x*Yau.pairing q V x*v x^2) :=
    ((hg.mul (Yau.pairing_smooth hq hV)).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiG : Integrable (fun x ↦ gamma x*realGradientSquare v x) :=
    (hg.mul (realGradientSquare_smooth v hv)).continuous.integrable_of_hasCompactSupport
      (realGradientSquare_compact v hc).mul_left
  have hiD : Integrable (fun x ↦ gamma x*realTransportDeformation B V v x) :=
    (hg.mul (realTransportDeformation_smooth B V v hB hV hv)).continuous.integrable_of_hasCompactSupport
      (realTransportDeformation_compact B V v hc).mul_left
  have hiE : Integrable (fun x ↦ gamma x*realMatrixEnergy B v v x) :=
    (hg.mul (realMatrixEnergy_smooth B hB v v hv hv)).continuous.integrable_of_hasCompactSupport
      (realMatrixEnergy_compact_left B v v hc).mul_left
  have hiR : Integrable (fun x ↦ gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) :=
    ((hg.mul (hv.pow 2)).mul (realWeightedElliptic_smooth gamma B _ hg hgn hB
      (Yau.weightedDiv_smooth hg hgn hV))).continuous.integrable_of_hasCompactSupport hvsq.mul_left.mul_right
  have hDpoint (x : Yau.Jets.Coord) : a*realGradientSquare v x ≤
      realTransportDeformation B V v x+s*realMatrixEnergy B v v x := by
    by_cases hx : x ∈ tsupport v
    · exact hquad x hx (realCoordGradient v x)
    · have hz := realCoordGradient_zero_off_support v hx
      have hd (i) : Yau.coordPartial v x i = 0 := congrFun hz i
      simp [realGradientSquare,realTransportDeformation,realMatrixEnergy_apply,hd]
  have hDi := integral_mono (hiG.const_mul a) (hiD.add (hiE.const_mul s))
    (fun x ↦ show a*(gamma x*realGradientSquare v x) ≤
      gamma x*realTransportDeformation B V v x+s*(gamma x*realMatrixEnergy B v v x) by
        nlinarith only [mul_le_mul_of_nonneg_left (hDpoint x) (hgp x).le])
  simp only [Pi.add_apply] at hDi
  rw [integral_const_mul,integral_add hiD (hiE.const_mul s),integral_const_mul] at hDi
  have hWi := integral_mono (hiv.const_mul b) (hiW.sub (hiq.const_mul s))
    (fun x ↦ show b*(gamma x*v x^2) ≤ gamma x*Yau.pairing q V x*v x^2-s*(gamma x*q x*v x^2) by
      by_cases hx : x ∈ tsupport v
      · nlinarith only [mul_le_mul_of_nonneg_left (hweight x hx) (mul_nonneg (hgp x).le (sq_nonneg (v x)))]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  simp only [Pi.sub_apply] at hWi
  rw [integral_const_mul,integral_sub hiW (hiq.const_mul s),integral_const_mul] at hWi
  have hRi := integral_mono hiR (hiv.const_mul C)
    (fun x ↦ show gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C*(gamma x*v x^2) by
      by_cases hx : x ∈ tsupport v
      · nlinarith only [mul_le_mul_of_nonneg_left (herror x hx) (mul_nonneg (hgp x).le (sq_nonneg (v x)))]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  rw [integral_const_mul] at hRi
  have hid := real_weighted_commutator_identity gamma q v B V hg hgn hq hv hc hB hs hV t
  rw [real_weighted_symmetric_shift gamma q v B hg hgn hq hv hc hB t (s*t)] at hid
  have hS0 : 0 ≤ ∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x+s*t*v x)^2 :=
    integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have hT0 : 0 ≤ t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) :=
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _)))
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have hDm := mul_le_mul_of_nonneg_left hDi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht0)
  have hWm := mul_le_mul_of_nonneg_left hWi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (pow_nonneg ht0 3))
  have hRm := mul_le_mul_of_nonneg_left hRi ht0
  have habs : s^2*t^2+C*t ≤ b*t^3 := by
    have h1 := mul_le_mul_of_nonneg_right hlarge ht0
    have h2 := mul_le_mul_of_nonneg_right h1 ht0
    have h3 := mul_nonneg hC (show 0 ≤ t^2-t by nlinarith only [ht])
    nlinarith only [h2,h3]
  have habsm := mul_le_mul_of_nonneg_right habs hv0
  nlinarith only [hid,hS0,hT0,hDm,hWm,hRm,habsm]

end
end Yau.Geometry

end OAI

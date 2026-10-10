import OAI.Analysis.LienardCycles.HeightSigns

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ModelAlgebra

noncomputable def wStar (m n l : ℝ) : ℝ :=
  2 * (l * m^4 - 2*l*m^3*n + 2*m*n^3 - n^4) / (m^2*n^2*(m+n))

noncomputable def dStar (m n l w S : ℝ) : ℝ :=
  (m-n)*S + (1-2*n/m+l*(2*m/n-1))*w + (m+n)/2*w^2

noncomputable def schwarzian (m n l b d : ℝ) : ℝ :=
  2*b*(m+n*l^2) + d^2/2*(l^2-1) - d*(1/m+l^2/n) +
    3/2*(l^2/n^2-1/m^2)

noncomputable def A (z l : ℝ) : ℝ := 2*l*z^3-3*l*z^2+3*z-2
noncomputable def T (z l : ℝ) : ℝ := 2*l*z^3-l*z^2-z+2
noncomputable def J (z l : ℝ) : ℝ := 2*l*z^4-2*l*z^3-l*z^2+z^2+2*z-2
noncomputable def S₀ (z l : ℝ) : ℝ := 3/2*(l^2-z⁻¹^2)

lemma A_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) : 0 < A z l := by
  have hz1 : 0 < z - 1 := by linarith
  have hA : A z l = (1-l)*(3*(z-1)+1) +
      l * (z-1) * (2*(z-1)^2+3*(z-1)+3) := by unfold A; ring
  rw [hA]
  positivity

lemma J_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) : 0 < J z l := by
  have hz1 : 0 < z - 1 := by linarith
  have hz2 : 0 < z + 1 := by linarith
  have hJ : J z l = (1-l)*((z-1)^2+4*(z-1)+1) +
      l * (2*(z-1)*(z+1)*((z-1)^2+(z-1)+1)) := by unfold J; ring
  rw [hJ]
  positivity

lemma wStar_normalized (z l : ℝ) :
    wStar z 1 l = 2*(l*z^3*(z-2)+2*z-1) / (z^2*(z+1)) := by
  unfold wStar
  congr 1 <;> ring

lemma wStar_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) :
    0 < wStar z 1 l := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z - 1 := by linarith
  have hz2 : 0 < z + 1 := by linarith
  rw [wStar_normalized]
  have heq : l*z^3*(z-2)+2*z-1 =
      (1-l)*(2*(z-1)+1)+l*(z-1)^3*(z+1) := by ring
  rw [heq]
  positivity

lemma baseline {z l : ℝ} (hz : 0 < z) :
    dStar z 1 l (wStar z 1 l) (S₀ z l) =
      (z-1)/(2*z^4) * A z l * T z l := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  unfold dStar S₀ A T
  rw [wStar_normalized]
  field_simp
  ring

lemma delta_factor {z l : ℝ} (hz : 0 < z) :
    1/z-l-wStar z 1 l = -(z-1)/((z+1)*z^2) * T z l := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [wStar_normalized]
  unfold T
  field_simp
  ring

lemma derivative_at_wStar {z l : ℝ} (hz : 0 < z) :
    (1-2/z+l*(2*z-1)) + (z+1)*wStar z 1 l = J z l / z^2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [wStar_normalized]
  unfold J
  field_simp
  ring

lemma dStar_mono_from_wStar {z l w S : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hw : wStar z 1 l ≤ w) :
    dStar z 1 l (wStar z 1 l) S ≤ dStar z 1 l w S := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z + 1 := by linarith
  have hp : 0 < 1-2/z+l*(2*z-1)+(z+1)*wStar z 1 l := by
    rw [derivative_at_wStar hz0]
    exact div_pos (J_pos hz hl hl1) (sq_pos_of_pos hz0)
  have heq : dStar z 1 l w S - dStar z 1 l (wStar z 1 l) S =
      (w-wStar z 1 l) * ((1-2/z+l*(2*z-1)+(z+1)*wStar z 1 l) +
        (z+1)/2*(w-wStar z 1 l)) := by unfold dStar; ring
  have hw0 : 0 ≤ w-wStar z 1 l := sub_nonneg.mpr hw
  have : 0 ≤ dStar z 1 l w S - dStar z 1 l (wStar z 1 l) S := by
    rw [heq]
    positivity
  linarith

lemma schwarzian_improvement (z l b d : ℝ) :
    schwarzian z 1 l b d - S₀ z l =
      (2*b*z-d^2/2)+l^2*(2*b+d^2/2-d)-d/z := by
  unfold schwarzian S₀
  simp only [div_one, one_pow, one_div]
  ring

lemma schwarzian_last (z l b d : ℝ) :
    schwarzian z 1 l b d =
      (2*b*z-d^2/2)+l^2*(2*b+d^2/2-d+3/2)-d/z-3/(2*z^2) := by
  unfold schwarzian
  simp only [div_one, one_pow]
  ring

lemma riccati_consequence {z l b d w : ℝ}
    (hl : 0 < l) (hd : d < 0) (hw : wStar z 1 l ≤ w)
    (hR : w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    2*Real.sqrt (d^2/4-b*z) < 1/z-l-wStar z 1 l := by
  have hdl : d*l < 0 := mul_neg_of_neg_of_pos hd hl
  linarith

lemma last_case_nonneg_T {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w) (hT : 0 ≤ T z l)
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z - 1 := by linarith
  have hdelta : 1/z-l-wStar z 1 l ≤ 0 := by
    rw [delta_factor hz0]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · exact hT
  have hd2 : d^2 < 4*b*z := by
    by_contra! h
    have hstrict := riccati_consequence hl hd hw (hRic h)
    have hs := Real.sqrt_nonneg (d^2/4-b*z)
    linarith
  have hbase : 0 ≤ dStar z 1 l (wStar z 1 l) (S₀ z l) := by
    rw [baseline hz0]
    exact mul_nonneg (mul_nonneg (by positivity) (A_pos hz hl hl1).le) hT
  have hS : 0 < schwarzian z 1 l b d - S₀ z l := by
    rw [schwarzian_improvement]
    have ht1 : 0 < 2*b*z-d^2/2 := by linarith
    have ht2 : 0 ≤ l^2*(2*b+d^2/2-d) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith only [sq_nonneg d, hb, hd]
    have ht3 : 0 < -(d/z) := by
      simpa only [neg_div] using div_pos (neg_pos.mpr hd) hz0
    linarith
  have heq : dStar z 1 l (wStar z 1 l) (schwarzian z 1 l b d) =
      dStar z 1 l (wStar z 1 l) (S₀ z l) +
        (z-1)*(schwarzian z 1 l b d - S₀ z l) := by unfold dStar; ring
  have hpos : 0 < dStar z 1 l (wStar z 1 l) (schwarzian z 1 l b d) := by
    rw [heq]
    exact add_pos_of_nonneg_of_pos hbase (mul_pos hz1 hS)
  exact hpos.trans_le (dStar_mono_from_wStar hz hl hl1 hw)

lemma negative_T_estimates {z l : ℝ} (hz : 1 < z) (hl : 0 < l)
    (hT : T z l < 0) : 2 < z ∧ 2+3*l < z := by
  have hz0 : 0 < z := by linarith
  have hzpow : 0 < z^2 := sq_pos_of_pos hz0
  have ht : 0 < l*z^2*(2*z-1) := mul_pos (mul_pos hl hzpow) (by linarith)
  have hTwo : 2 < z := by unfold T at hT; nlinarith only [hT, ht]
  have hSquare : 4 < z^2 := by nlinarith only [hTwo]
  have hrest : 0 < z^2*(2*z-1)-3 := by
    have : 0 < z^2*(2*z-4) := mul_pos hzpow (by linarith)
    nlinarith only [this, hSquare]
  have hprod : 0 < l * (z^2*(2*z-1)-3) := mul_pos hl hrest
  exact ⟨hTwo, by unfold T at hT; nlinarith only [hT, hprod]⟩

lemma slope_estimate {z l d : ℝ} (hz : 0 < z) (hl : 0 < l)
    (hzl : 2 + 3*l < z) (hX : d < (l/z-1)/(1+l)) : 2 < -d*z := by
  have hl1 : 0 < 1+l := by linarith
  have h1 : d*(1+l) < l/z-1 := (lt_div_iff₀ hl1).mp hX
  have h2 := mul_lt_mul_of_pos_right h1 hz
  have heq : (l/z-1)*z = l-z := by field_simp
  rw [heq] at h2
  have hh : (2+d*z)*(1+l) < 0 := by nlinarith only [h2, hzl]
  have hneg : 2+d*z < 0 := by
    by_contra hn
    have hnonneg := mul_nonneg (le_of_not_gt hn) hl1.le
    linarith only [hnonneg, hh]
  linarith

lemma last_case_neg_T {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w) (hT : T z l < 0)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hzsq : 0 < z^2 := sq_pos_of_pos hz0
  obtain ⟨hz2, hzl⟩ := negative_T_estimates hz hl hT
  have hdz : 2 < -d*z := slope_estimate hz0 hl hzl hX
  have hddiv : 2/z^2 < -d/z := by
    have heq : -d/z = (-d*z)/z^2 := by field_simp
    rw [heq]
    exact div_lt_div_of_pos_right hdz hzsq
  have hfirst : -(1/(2*z^2)) < 2*b*z-d^2/2 := by
    by_cases hnonneg : 0 ≤ 2*b*z-d^2/2
    · have : 0 < 1/(2*z^2) := by positivity
      linarith
    · have hlarge : 4*b*z ≤ d^2 := by linarith
      have hrad : 0 ≤ d^2/4-b*z := by linarith
      have hroot := Real.sq_sqrt hrad
      have hroot0 := Real.sqrt_nonneg (d^2/4-b*z)
      have hstrict := riccati_consequence hl hd hw (hRic hlarge)
      have hws := wStar_pos hz hl hl1
      have hupper : 2*Real.sqrt (d^2/4-b*z) < 1/z := by linarith
      have hrecip : 0 < 1/z := by positivity
      have hsquare : 4*(Real.sqrt (d^2/4-b*z))^2 < (1/z)^2 := by
        nlinarith only [sq_nonneg (2*Real.sqrt (d^2/4-b*z)-1/z),
          mul_pos (by linarith : 0 < 1/z-2*Real.sqrt (d^2/4-b*z))
            (by linarith : 0 < 1/z+2*Real.sqrt (d^2/4-b*z))]
      have heq : (1/z)^2 = 1/z^2 := by ring
      rw [heq] at hsquare
      have heq2 : 1/(2*z^2) = (1/z^2)/2 := by ring
      rw [heq2]
      nlinarith only [hsquare, hroot]
  have hS : 0 < schwarzian z 1 l b d := by
    rw [schwarzian_last]
    have hterm : 0 ≤ l^2*(2*b+d^2/2-d+3/2) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith only [sq_nonneg d, hb, hd]
    have heq : 3/(2*z^2) = -(1/(2*z^2))+2/z^2 := by ring
    rw [heq]
    simp only [neg_div] at hddiv
    linarith
  have hwpos : 0 < w := (wStar_pos hz hl hl1).trans_le hw
  have hcoeff : 0 < 1-2/z+l*(2*z-1) := by
    have hdiv : 2/z < 1 := (div_lt_one hz0).mpr hz2
    have : 0 < l*(2*z-1) := mul_pos hl (by linarith)
    linarith
  unfold dStar
  simp only [mul_one, div_one]
  have : 0 < z-1 := by linarith
  positivity

lemma last_case {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  rcases le_or_gt 0 (T z l) with hT | hT
  · exact last_case_nonneg_T hz hl hl1 hb hd hw hT hRic
  · exact last_case_neg_T hz hl hl1 hb hd hw hT hX hRic

lemma wStar_neg {z l : ℝ} (hz : 0 < z) (hz1 : z < 1) (hl : 1 ≤ l) :
    wStar z 1 l < 0 := by
  rw [wStar_normalized]
  have ht : z^3*(z-2) < 0 := mul_neg_of_pos_of_neg (pow_pos hz _) (by linarith)
  have hb : l*z^3*(z-2) ≤ z^3*(z-2) := by
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) ht.le]
  have heq : z^3*(z-2)+2*z-1 = (z-1)^3*(z+1) := by ring
  have hbase : z^3*(z-2)+2*z-1 < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos ((show Odd (3 : ℕ) by decide).pow_neg (by linarith)) (by positivity)
  apply div_neg_of_neg_of_pos _ (by positivity)
  linarith

lemma equal_endpoints_pos {l w S : ℝ} (hl : 1 < l) (hw : 0 < w) :
    0 < dStar 1 1 l w S := by
  have heq : dStar 1 1 l w S = (l-1)*w+w^2 := by unfold dStar; ring
  rw [heq]
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hw) (sq_nonneg _)

lemma schwarzian_pos_of_one_le {z l b d : ℝ}
    (hz : 1 < z) (hl : 1 ≤ l) (hb : 0 < b) (hd : d < 0) :
    0 < schwarzian z 1 l b d := by
  have hz0 : 0 < z := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hl2 : 1 ≤ l^2 := by nlinarith
  have hz2 : 1 < z^2 := by nlinarith
  have hiz : 1/z^2 < 1 := (div_lt_one (sq_pos_of_pos hz0)).mpr hz2
  have hi : 0 < 1/z+l^2 := add_pos_of_pos_of_nonneg (one_div_pos.mpr hz0) (sq_nonneg _)
  have h1 : 0 < 2*b*(z+l^2) := mul_pos (by positivity) (by positivity)
  have h2 : 0 ≤ d^2/2*(l^2-1) := mul_nonneg (by positivity) (by linarith)
  have h3 : 0 < -d*(1/z+l^2) := mul_pos (neg_pos.mpr hd) hi
  have h4 : 0 < (3:ℝ)/2*(l^2-1/z^2) := mul_pos (by norm_num) (by linarith)
  unfold schwarzian
  simp only [one_pow, div_one]
  linarith

lemma second_case {z l b d w : ℝ}
    (hz : 1 < z) (hl : 1 ≤ l) (hb : 0 < b) (hd : d < 0) (hw : 0 ≤ w) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hlow : l*(2*z-1) ≥ 2*z-1 := by
    have := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 2*z-1 by linarith)
    nlinarith only [this]
  have hi : 2/z < 2 := (div_lt_iff₀ hz0).mpr (by linarith)
  have hcoeff : 0 < 1-2/z+l*(2*z-1) := by linarith
  have hS := schwarzian_pos_of_one_le hz hl hb hd
  unfold dStar
  simp only [div_one, mul_one]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos (by linarith) hS) (mul_nonneg hcoeff.le hw))
    (mul_nonneg (by positivity) (sq_nonneg _))

lemma zero_sign {z l b d w : ℝ}
    (hz : 0 < z) (hl : 0 < l) (hb : 0 < b)
    (hSmall : z ≤ 1 → 1 < l ∧ 0 < w)
    (hLarge : 1 < z → d < 0)
    (hSlope : 1 < z → 1 ≤ l → 0 ≤ w)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 4*b*z ≤ d^2 → w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z))
    (hZero : dStar z 1 l w (schwarzian z 1 l b d) = 0) :
    z ≠ 1 ∧ 0 < (wStar z 1 l-w)/(z-1) := by
  rcases lt_trichotomy z 1 with hlt | rfl | hgt
  · obtain ⟨hl1, hw⟩ := hSmall hlt.le
    refine ⟨ne_of_lt hlt, div_pos_of_neg_of_neg ?_ (by linarith)⟩
    have hstar := wStar_neg hz hlt hl1.le
    linarith
  · obtain ⟨hl1, hw⟩ := hSmall le_rfl
    have := equal_endpoints_pos (S := schwarzian 1 1 l b d) hl1 hw
    simp only [hZero, lt_self_iff_false] at this
  · have hd := hLarge hgt
    have hl1 : l < 1 := by
      by_contra! hl1
      have := second_case hgt hl1 hb hd (hSlope hgt hl1)
      linarith
    have hw : w < wStar z 1 l := by
      by_contra! hw
      have := last_case hgt hl hl1 hb hd hw hX hRic
      linarith
    exact ⟨ne_of_gt hgt, div_pos (sub_pos.mpr hw) (by linarith)⟩

end QuinticLienard.ModelAlgebra

end OAI

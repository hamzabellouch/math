import OAI.Analysis.LienardCycles.EndpointJets

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
lemma zero_sign_conditional {z l b d w : ℝ}
    (hz : 0 < z) (hl : 0 < l) (hb : 0 < b)
    (hSmall : z ≤ 1 → 1 < l ∧ 0 < w)
    (hLarge : 1 < z → d < 0)
    (hSlope : 1 < z → 1 ≤ l → 0 ≤ w)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 1 < z → 4*b*z ≤ d^2 → w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z))
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
      have := last_case hgt hl hl1 hb hd hw hX (hRic hgt)
      linarith
    exact ⟨ne_of_gt hgt, div_pos (sub_pos.mpr hw) (by linarith)⟩

lemma schwarzian_scaling {m n l b d : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) :
    schwarzian (m/n) 1 l (n^3*b) (n*d)=n^2*schwarzian m n l b d := by
  dsimp [schwarzian]
  field_simp
lemma dStar_scaling {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) :
    dStar (m/n) 1 l (n*w) (n^2*s)=n*dStar m n l w s := by
  dsimp [dStar]
  field_simp
lemma wStar_scaling {m n l : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hs : m+n ≠ 0) :
    wStar (m/n) 1 l=n*wStar m n l := by
  dsimp [wStar]
  field_simp
lemma X_scaling {m n l : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    (l/(m/n)-1)/(1+l)=n*((l/m-1/n)/(1+l)) := by
  field_simp

lemma zero_sign_unscaled {m n l b d w : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hl : 0 < l) (hb : 0 < b)
    (hSmall : m ≤ n → 1 < l ∧ 0 < w)
    (hLarge : n < m → d < 0)
    (hSlope : n < m → 1 ≤ l → 0 ≤ w)
    (hX : d < (l/m-1/n)/(1+l))
    (hRic : n < m → 4*b*m ≤ d^2 → w ≤ 1/m-l/n+d*l-2*Real.sqrt (d^2/4-b*m))
    (hZero : dStar m n l w (schwarzian m n l b d) = 0) :
    m ≠ n ∧ 0 < (wStar m n l-w)/(m-n) := by
  have hz := div_pos hm hn
  have hlt : 1 < m/n ↔ n < m := by simpa using (lt_div_iff₀ hn : 1 < m/n ↔ 1*n < m)
  have hle : m/n ≤ 1 ↔ m ≤ n := by simpa using (div_le_iff₀ hn : m/n ≤ 1 ↔ m ≤ 1*n)
  have hs : m+n ≠ 0 := ne_of_gt (add_pos hm hn)
  have hln : 1+l ≠ 0 := by positivity
  have hsmall : m/n ≤ 1 → 1 < l ∧ 0 < n*w := by
    intro h
    exact ⟨(hSmall (hle.mp h)).1,mul_pos hn (hSmall (hle.mp h)).2⟩
  have hlarge : 1 < m/n → n*d < 0 := fun h => mul_neg_of_pos_of_neg hn (hLarge (hlt.mp h))
  have hslope : 1 < m/n → 1 ≤ l → 0 ≤ n*w :=
    fun h hl1 => mul_nonneg hn.le (hSlope (hlt.mp h) hl1)
  have hx : n*d < (l/(m/n)-1)/(1+l) := by
    rw [X_scaling (ne_of_gt hm) (ne_of_gt hn) hln]
    exact mul_lt_mul_of_pos_left hX hn
  have hric : 1 < m/n → 4*(n^3*b)*(m/n) ≤ (n*d)^2 →
      n*w ≤ 1/(m/n)-l+n*d*l-2*Real.sqrt ((n*d)^2/4-(n^3*b)*(m/n)) := by
    intro hz1 hdisc
    have he : 4*(n^3*b)*(m/n)=n^2*(4*b*m) := by field_simp
    have he2 : (n*d)^2=n^2*d^2 := by ring
    rw [he,he2] at hdisc
    have hd := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hdisc
    have hh := mul_le_mul_of_nonneg_left (hRic (hlt.mp hz1) hd) hn.le
    have hroot : Real.sqrt ((n*d)^2/4-(n^3*b)*(m/n))=n*Real.sqrt (d^2/4-b*m) := by
      have heq : (n*d)^2/4-(n^3*b)*(m/n)=n^2*(d^2/4-b*m) := by field_simp
      rw [heq,Real.sqrt_mul (sq_nonneg n),Real.sqrt_sq hn.le]
    rw [hroot]
    convert! hh using 1
    field_simp
  have hzero : dStar (m/n) 1 l (n*w) (schwarzian (m/n) 1 l (n^3*b) (n*d))=0 := by
    rw [schwarzian_scaling (ne_of_gt hm) (ne_of_gt hn),dStar_scaling (ne_of_gt hm) (ne_of_gt hn),hZero,mul_zero]
  obtain ⟨hne,hpos⟩ := zero_sign_conditional hz hl (mul_pos (pow_pos hn _) hb)
    hsmall hlarge hslope hx hric hzero
  have hmn : m ≠ n := by intro h; apply hne; rw [h,div_self (ne_of_gt hn)]
  refine ⟨hmn,?_⟩
  have heq : (wStar (m/n) 1 l-n*w)/(m/n-1)=n^2*((wStar m n l-w)/(m-n)) := by
    rw [wStar_scaling (ne_of_gt hm) (ne_of_gt hn) hs]
    field_simp
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos (sq_nonneg n)
end QuinticLienard.ModelAlgebra

end OAI

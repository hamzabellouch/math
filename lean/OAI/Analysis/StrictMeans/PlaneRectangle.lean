import OAI.Analysis.StrictMeans.CompactMorseIndex

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def planeRectangle (o : ℂ) (A B : ℝ) : Set ℂ :=
  {z | |z.re-o.re|≤A ∧ |z.im-o.im|≤B}

lemma compact_planeRectangle (o : ℂ) (A B : ℝ) : IsCompact (planeRectangle o A B) := by
  have hc : IsClosed (planeRectangle o A B) :=
    (isClosed_le ((Complex.continuous_re.sub continuous_const).abs) continuous_const).inter
    (isClosed_le ((Complex.continuous_im.sub continuous_const).abs) continuous_const)
  apply (isCompact_closedBall o (A+B)).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z-o)).trans (add_le_add hz.1 hz.2)

lemma compact_halfPlane_rectangle {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ∀ z∈K, 0<z.im) :
    ∃ (o : ℂ) (A B δ : ℝ), 0<A ∧ 0<B ∧ 0<δ ∧
      (∀ z∈K, |z.re-o.re|+δ≤A ∧ |z.im-o.im|+δ≤B) ∧
      (∀ z∈planeRectangle o A B, 0<z.im) := by
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  let a := p.im
  have ha : 0<a := hH p hp
  have haR : a≤R := (Complex.im_le_norm p).trans (hR p hp)
  let o : ℂ := ((a+R)/2:ℂ)*Complex.I
  let δ := min 1 (a/4)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  refine ⟨o,R+1,R/2,δ,by linarith,by linarith,hδ,?_,?_⟩
  · intro z hz
    have hzR := hR z hz
    have hzA := (Complex.abs_re_le_norm z).trans hzR
    have hzB := (Complex.im_le_norm z).trans hzR
    have haz : a≤z.im := hmin hz
    have hδ₁ : δ≤1 := min_le_left _ _
    have hδ₂ : δ≤a/4 := min_le_right _ _
    have hor : o.re=0 := by simp [o]
    have hoi : o.im=(a+R)/2 := by simp [o]
    rw [hor,hoi,sub_zero]
    constructor
    · linarith
    · have hab : |z.im-(a+R)/2|≤(R-a)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
      linarith
  · intro z hz
    have hoi : o.im=(a+R)/2 := by simp [o]
    have hh := (abs_le.mp hz.2).1
    rw [hoi] at hh
    linarith

lemma meshPoint_re (o : ℂ) (s : ℝ) (v : Lattice) :
    (meshPoint o s v).re=o.re+s*((ofLex v).1:ℝ) := by simp [meshPoint]
lemma meshPoint_im (o : ℂ) (s : ℝ) (v : Lattice) :
    (meshPoint o s v).im=o.im+s*((ofLex v).2:ℝ) := by simp [meshPoint]

lemma meshPoint_near (o z : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ v : Lattice, dist (meshPoint o s v) z < 2*s := by
  let i : ℤ := ⌊(z.re-o.re)/s⌋
  let j : ℤ := ⌊(z.im-o.im)/s⌋
  let v : Lattice := toLex (i,j)
  have hi : s*(i:ℝ)≤z.re-o.re ∧ z.re-o.re<s*((i:ℝ)+1) := by
    constructor
    · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Int.floor_le _)
    · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _) |>.trans_eq (mul_comm _ _)
  have hj : s*(j:ℝ)≤z.im-o.im ∧ z.im-o.im<s*((j:ℝ)+1) := by
    constructor
    · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Int.floor_le _)
    · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _) |>.trans_eq (mul_comm _ _)
  have hvx : |(meshPoint o s v-z).re|<s := by
    rw [Complex.sub_re,meshPoint_re]
    change |o.re+s*(i:ℝ)-z.re|<s
    exact abs_lt.mpr ⟨by linarith [hi.2],by linarith [hi.1]⟩
  have hvy : |(meshPoint o s v-z).im|<s := by
    rw [Complex.sub_im,meshPoint_im]
    change |o.im+s*(j:ℝ)-z.im|<s
    exact abs_lt.mpr ⟨by linarith [hj.2],by linarith [hj.1]⟩
  refine ⟨v,?_⟩
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by linarith)

lemma meshPoint_hits_interior {K : Set ℂ} (hne : (interior K).Nonempty) (o : ℂ) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∃ v, meshPoint o s v∈K := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  filter_upwards [gt_mem_nhds (show (0:ℝ)<r/2 by positivity)] with s hs
  intro hspos
  obtain ⟨v,hv⟩ := meshPoint_near o z hspos
  exact ⟨v,hball (show meshPoint o s v∈Metric.ball z r by rw [Metric.mem_ball]; linarith)⟩

end
end StrictInverseFirstPower.Grid

end

end OAI

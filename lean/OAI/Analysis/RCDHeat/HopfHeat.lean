import Mathlib
import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HopfHeat. -/




open Set Metric Filter
open scoped Topology NNReal

namespace RegularPointCoordinates
section HopfLax

variable {X : Type*} [MetricSpace X]

 
noncomputable def hopfLax (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sInf (range (fun y => f y + dist x y ^ 2 / (2*t)))

 theorem hopfLax_cost_lower {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (x y : X) :
    f x - t*(L:ℝ)^2/2 ≤ f y + dist x y^2/(2*t) := by
  have hLip := (abs_le.mp (show |f x-f y| ≤ (L:ℝ)*dist x y from hf.dist_le_mul x y)).2
  have hsq := sq_nonneg (dist x y-t*(L:ℝ))
  have hquad : -(t*(L:ℝ)^2/2) ≤ dist x y^2/(2*t)-(L:ℝ)*dist x y := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*t)).mp
    have he : (dist x y^2/(2*t)-(L:ℝ)*dist x y)*(2*t) =
        dist x y^2-2*t*(L:ℝ)*dist x y := by field_simp
    rw [he]
    nlinarith
  linarith

 theorem hopfLax_bddBelow {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (x : X) :
    BddBelow (range (fun y => f y + dist x y^2/(2*t))) := by
  refine ⟨f x-t*(L:ℝ)^2/2,?_⟩
  rintro _ ⟨y,rfl⟩
  exact hopfLax_cost_lower hf ht x y

 theorem hopfLax_le_cost {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (x y : X) :
    hopfLax f t x ≤ f y + dist x y^2/(2*t) :=
  csInf_le (hopfLax_bddBelow hf ht x) (mem_range_self y)

 theorem hopfLax_bounds {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (x : X) :
    f x-t*(L:ℝ)^2/2 ≤ hopfLax f t x ∧ hopfLax f t x ≤ f x := by
  refine ⟨le_csInf ⟨_,mem_range_self x⟩ ?_,?_⟩
  · rintro _ ⟨y,rfl⟩
    exact hopfLax_cost_lower hf ht x y
  · simpa using hopfLax_le_cost hf ht x x

 theorem hopfLax_antitone_time {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f t x ≤ hopfLax f s x := by
  apply le_csInf ⟨_,mem_range_self x⟩
  rintro _ ⟨y,rfl⟩
  exact (hopfLax_le_cost hf (hs.trans_le hst) x y).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg (dist x y)) (by linarith : 0 < 2*s)
      (by linarith : 2*s ≤ 2*t)))

 
theorem hopfLax_exists_minimizer [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    ∃ y : X, hopfLax f t x = f y + dist x y^2/(2*t) ∧ dist x y ≤ 2*t*(L:ℝ) := by
  let R := 2*t*(L:ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : Continuous (fun y => f y + dist x y^2/(2*t)) := hf.continuous.add
    ((continuous_const.dist continuous_id).pow 2 |>.div_const _)
  obtain ⟨y,hy,hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x,mem_closedBall_self hR.le⟩ hc.continuousOn
  have hycost : f y+dist x y^2/(2*t) ≤ f x := by
    simpa using hmin (mem_closedBall_self hR.le)
  have hdist : dist x y ≤ 2*t*(L:ℝ) := by
    have hLip := (abs_le.mp (show |f x-f y| ≤ (L:ℝ)*dist x y from hf.dist_le_mul x y)).2
    have hq : dist x y^2/(2*t) ≤ (L:ℝ)*dist x y := by linarith
    have hq' := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hq
    by_contra h
    have hh : 2*t*(L:ℝ) < dist x y := lt_of_not_ge h
    have hd : 0 < dist x y := lt_of_le_of_lt (by positivity) hh
    nlinarith
  refine ⟨y,le_antisymm (hopfLax_le_cost hf ht x y) ?_,hdist⟩
  apply le_csInf ⟨_,mem_range_self x⟩
  rintro _ ⟨z,rfl⟩
  by_cases hz : z ∈ closedBall x R
  · exact hmin hz
  · have hzr : 2*t*(L:ℝ) < dist x z := by
      have hz' : R < dist x z := by simpa [mem_closedBall, dist_comm, not_le] using hz
      dsimp [R] at hz'
      linarith
    have hLip := (abs_le.mp (show |f x-f z| ≤ (L:ℝ)*dist x z from hf.dist_le_mul x z)).2
    have hq : (L:ℝ)*dist x z ≤ dist x z^2/(2*t) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
      nlinarith [mul_nonneg (dist_nonneg (x := x) (y := z)) (sub_nonneg.mpr hzr.le)]
    linarith

 
theorem hopfLax_difference_upper [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x z : X) :
    hopfLax f t z - hopfLax f t x ≤
      2*(L:ℝ)*dist x z+dist x z^2/(2*t) := by
  obtain ⟨y,hy,hd⟩ := hopfLax_exists_minimizer hf ht x
  have hz := hopfLax_le_cost hf ht z y
  have htri : dist z y ≤ dist x z+dist x y := by
    simpa only [dist_comm z x] using dist_triangle z x y
  have hs := pow_le_pow_left₀ dist_nonneg htri 2
  rw [hy]
  have hcost : dist z y^2/(2*t)-dist x y^2/(2*t) ≤
      2*(L:ℝ)*dist x z+dist x z^2/(2*t) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*t)).mp
    have he : (dist z y^2/(2*t)-dist x y^2/(2*t))*(2*t) = dist z y^2-dist x y^2 := by
      field_simp
    rw [he]
    have he' : (2*(L:ℝ)*dist x z+dist x z^2/(2*t))*(2*t) =
        4*t*(L:ℝ)*dist x z+dist x z^2 := by field_simp; ring
    rw [he']
    nlinarith [mul_le_mul_of_nonneg_right hd (dist_nonneg (x := x) (y := z))]
  linarith

 theorem hopfLax_abs_difference [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x z : X) :
    |hopfLax f t z - hopfLax f t x| ≤
      2*(L:ℝ)*dist x z+dist x z^2/(2*t) := by
  refine abs_le.mpr ⟨?_,hopfLax_difference_upper hf ht x z⟩
  have h := hopfLax_difference_upper hf ht z x
  rw [dist_comm z x] at h
  linarith

 theorem hopfLax_minimizer_dist {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) {x y : X}
    (hy : hopfLax f t x = f y+dist x y^2/(2*t)) : dist x y ≤ 2*t*(L:ℝ) := by
  have hb := (hopfLax_bounds hf ht x).2
  rw [hy] at hb
  have hLip := (abs_le.mp (show |f x-f y| ≤ (L:ℝ)*dist x y from hf.dist_le_mul x y)).2
  have hq : dist x y^2/(2*t) ≤ (L:ℝ)*dist x y := by linarith
  have hq' := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hq
  by_contra h
  have hh : 2*t*(L:ℝ) < dist x y := lt_of_not_ge h
  have hd : 0 < dist x y := lt_of_le_of_lt (by positivity) hh
  nlinarith

 theorem hopfLax_continuous [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) : Continuous (hopfLax f t) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let C := 2*(L:ℝ)+1/(2*t)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min 1 (ε/C),lt_min zero_lt_one (div_pos hε hC),?_⟩
  intro z hz
  have hd1 : dist x z < 1 := by simpa only [dist_comm x z] using hz.trans_le (min_le_left _ _)
  have hdε : dist x z < ε/C := by simpa only [dist_comm x z] using hz.trans_le (min_le_right _ _)
  have hsq : dist x z^2/(2*t) ≤ dist x z/(2*t) :=
    div_le_div_of_nonneg_right (by nlinarith [dist_nonneg (x := x) (y := z)]) (by positivity)
  have hmul := (lt_div_iff₀ hC).mp hdε
  have hb := hopfLax_abs_difference hf ht x z
  rw [Real.dist_eq]
  dsimp [C] at hmul
  simp only [div_eq_mul_inv, one_mul] at hsq hmul hb
  nlinarith [dist_nonneg (x := x) (y := z)]

 def hopfMinimizers (f : X → ℝ) (t : ℝ) (x : X) : Set X :=
  {y | hopfLax f t x = f y+dist x y^2/(2*t)}

 theorem hopfMinimizers_nonempty [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    (hopfMinimizers f t x).Nonempty := by
  obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hf ht x
  exact ⟨y,hy⟩

 theorem hopfMinimizers_compact [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    IsCompact (hopfMinimizers f t x) := by
  apply (isCompact_closedBall x (2*t*(L:ℝ))).of_isClosed_subset
  · exact isClosed_eq continuous_const
      (hf.continuous.add ((continuous_const.dist continuous_id).pow 2 |>.div_const _))
  · intro y hy
    rw [mem_closedBall, dist_comm]
    exact hopfLax_minimizer_dist hf ht hy

 
noncomputable def hopfRadius (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sSup ((fun y => dist x y) '' hopfMinimizers f t x)

 theorem hopfRadius_attained [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    ∃ y ∈ hopfMinimizers f t x, hopfRadius f t x = dist x y := by
  have hc := (hopfMinimizers_compact hf ht x).image
    (show Continuous (fun y => dist x y) from continuous_const.dist continuous_id)
  obtain ⟨y,hy,he⟩ := hc.sSup_mem ((hopfMinimizers_nonempty hf ht x).image _)
  exact ⟨y,hy,he.symm⟩

 theorem hopfRadius_bounds [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    0 ≤ hopfRadius f t x ∧ hopfRadius f t x ≤ 2*t*(L:ℝ) := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf ht x
  rw [he]
  exact ⟨dist_nonneg,hopfLax_minimizer_dist hf ht hy⟩

 theorem dist_le_hopfRadius [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) {x y : X}
    (hy : y ∈ hopfMinimizers f t x) : dist x y ≤ hopfRadius f t x := by
  unfold hopfRadius
  apply le_csSup _ (show dist x y ∈ (fun z => dist x z) '' hopfMinimizers f t x from ⟨y,hy,rfl⟩)
  refine ⟨2*t*(L:ℝ),?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact hopfLax_minimizer_dist hf ht hz

 

theorem hopfRadius_upperSemicontinuous [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : X, dist z x < δ →
      hopfRadius f t z < hopfRadius f t x + ε := by
  by_contra h
  push Not at h
  have hex (i : ℕ) : ∃ z : X, dist z x < 1/(i+1:ℝ) ∧
      hopfRadius f t x+ε ≤ hopfRadius f t z := h _ (by positivity)
  choose z hz hd using hex
  choose y hy he using fun i => hopfRadius_attained hf ht (z i)
  have hzt : Tendsto z atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun i => (hz i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hymem (i : ℕ) : y i ∈ closedBall x (1+2*t*(L:ℝ)) := by
    have hb := hopfLax_minimizer_dist hf ht (hy i)
    have hi : (1:ℝ)/(i+1:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
    have htri := dist_triangle x (z i) (y i)
    rw [mem_closedBall, dist_comm]
    rw [dist_comm x (z i)] at htri
    linarith [hz i]
  obtain ⟨a,_,φ,hφ,hya⟩ := (isCompact_closedBall x (1+2*t*(L:ℝ))).tendsto_subseq hymem
  have hzφ := hzt.comp hφ.tendsto_atTop
  have hcost := (hf.continuous.tendsto a |>.comp hya).add
    ((hzφ.dist hya).pow 2 |>.div_const (2*t))
  have hQt := (hopfLax_continuous hf ht).tendsto x |>.comp hzφ
  have ha : a ∈ hopfMinimizers f t x := by
    exact tendsto_nhds_unique hQt (hcost.congr' (Eventually.of_forall fun i => (hy (φ i)).symm))
  have hbad : hopfRadius f t x+ε ≤ dist x a := by
    exact ge_of_tendsto (hzφ.dist hya) (Eventually.of_forall fun i => by
      change hopfRadius f t x+ε ≤ dist (z (φ i)) (y (φ i))
      rw [← he (φ i)]; exact hd (φ i))
  have hgood := dist_le_hopfRadius hf ht ha
  linarith

end HopfLax
open Set Metric Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X]

 theorem hopfLax_difference_radius [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x z : X) :
    hopfLax f t z-hopfLax f t x ≤ hopfRadius f t x / t * dist x z+dist x z^2/(2*t) := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf ht x
  have hz := hopfLax_le_cost hf ht z y
  change hopfLax f t x = f y+dist x y^2/(2*t) at hy
  have htri : dist z y ≤ dist x z+dist x y := by
    simpa only [dist_comm z x] using dist_triangle z x y
  have hs := pow_le_pow_left₀ dist_nonneg htri 2
  rw [hy,he]
  have hcost : dist z y^2/(2*t)-dist x y^2/(2*t) ≤
      dist x y/t*dist x z+dist x z^2/(2*t) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*t)).mp
    have he₁ : (dist z y^2/(2*t)-dist x y^2/(2*t))*(2*t) = dist z y^2-dist x y^2 := by
      field_simp
    have he₂ : (dist x y/t*dist x z+dist x z^2/(2*t))*(2*t) =
        2*dist x y*dist x z+dist x z^2 := by field_simp
    rw [he₁,he₂]
    nlinarith
  linarith

 theorem hopfLax_slope_le_eps [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) (ε : ℝ) (hε : 0 < ε) :
    localSlope (hopfLax f t) x ≤ ENNReal.ofReal ((hopfRadius f t x+ε)/t+ε/(2*t)) := by
  obtain ⟨δ,hδ,hδrad⟩ := hopfRadius_upperSemicontinuous hf ht x ε hε
  refine iInf_le_of_le (min δ ε) (iInf_le_of_le (lt_min hδ hε) ?_)
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (dist_pos.mpr (Ne.symm hyx))).mpr
  have hxyε := hy.trans_le (min_le_right _ _)
  have hradius := hδrad y (by simpa only [dist_comm x y] using hy.trans_le (min_le_left _ _))
  have hu := hopfLax_difference_radius hf ht x y
  have hl := hopfLax_difference_radius hf ht y x
  rw [dist_comm y x] at hl
  have hq : dist x y^2/(2*t) ≤ ε/(2*t)*dist x y := by
    rw [mul_comm (ε/(2*t)), ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hR : hopfRadius f t y/t*dist x y ≤ (hopfRadius f t x+ε)/t*dist x y :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hradius.le ht.le) dist_nonneg
  have hR' : hopfRadius f t x/t*dist x y ≤ (hopfRadius f t x+ε)/t*dist x y :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ht.le) dist_nonneg
  apply abs_le.mpr
  constructor <;> nlinarith

 
theorem hopfLax_slope_le [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 < t) (x : X) :
    localSlope (hopfLax f t) x ≤ ENNReal.ofReal (hopfRadius f t x/t) := by
  have hc : Continuous (fun ε : ℝ => ENNReal.ofReal ((hopfRadius f t x+ε)/t+ε/(2*t))) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim := (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hh : ∀ᶠ ε : ℝ in 𝓝[>] 0, localSlope (hopfLax f t) x ≤
      ENNReal.ofReal ((hopfRadius f t x+ε)/t+ε/(2*t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hopfLax_slope_le_eps hf ht x ε hε
  simpa using ge_of_tendsto hlim hh

 theorem hopfLax_time_derivative [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t d : ℝ} (ht : 0 < t) (x : X)
    (hder : HasDerivAt (fun s => hopfLax f s x) d t) :
    d = -(hopfRadius f t x)^2/(2*t^2) := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf ht x
  have hcost : HasDerivAt (fun s : ℝ => f y+dist x y^2/(2*s))
      (-(dist x y)^2/(2*t^2)) t := by
    convert (hasDerivAt_const t (f y)).add
      ((hasDerivAt_const t (dist x y^2)).div ((hasDerivAt_id t).const_mul 2)
        (by positivity)) using 1
    all_goals first | rfl | (dsimp; ring)
  have hmax : IsLocalMax (fun s => hopfLax f s x-(f y+dist x y^2/(2*s))) t := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change hopfLax f t x = f y+dist x y^2/(2*t) at hy
    rw [hy,sub_self]
    exact sub_nonpos.mpr (hopfLax_le_cost hf hs x y)
  have hd := hmax.hasDerivAt_eq_zero (hder.sub hcost)
  rw [he]
  linarith

 
theorem hopfLax_hamiltonJacobi [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {t d : ℝ} (ht : 0 < t) (x : X)
    (hder : HasDerivAt (fun s => hopfLax f s x) d t) :
    d+(localSlope (hopfLax f t) x).toReal^2/2 ≤ 0 := by
  have hs := hopfLax_slope_le hf ht x
  have hR := (hopfRadius_bounds hf ht x).1
  have hfin : localSlope (hopfLax f t) x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hs' := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hs
  rw [ENNReal.toReal_ofReal (div_nonneg hR ht.le)] at hs'
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hs' 2
  rw [hopfLax_time_derivative hf ht x hder]
  rw [div_pow] at hsq
  rw [mul_comm 2 (t^2), div_mul_eq_div_div, neg_div]
  linarith

 theorem hopfLax_minimizer_dist_sharp {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {t : ℝ} (ht : 0 < t) {x y : X}
    (hy : hopfLax f t x = f y+dist x y^2/(2*t)) : dist x y ≤ t*(L:ℝ) := by
  by_cases hxy : x = y
  · subst y
    simp only [dist_self]
    positivity
  have hr : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨γ,hγ0,hγ1,hγ⟩ := hgeo x y
  have hparam : ∀ u : ℝ, 0 ≤ u → u < 1 → dist x y*(1+u) ≤ 2*t*(L:ℝ) := by
    intro u hu hu1
    let U : Time := ⟨u,hu,hu1.le⟩
    have hdp : dist x (γ U) = u*dist x y := by
      rw [← hγ0,hγ]
      change |0-u| *dist (γ 0) (γ 1) = u*dist (γ 0) y
      rw [hγ1,zero_sub,abs_neg,abs_of_nonneg hu]
    have hdq : dist (γ U) y = (1-u)*dist x y := by
      rw [← hγ1,hγ]
      change |u-1| *dist (γ 0) (γ 1) = (1-u)*dist x (γ 1)
      rw [hγ0,abs_of_nonpos (by linarith)]
      ring
    have hLip := (abs_le.mp (show |f (γ U)-f y| ≤ (L:ℝ)*dist (γ U) y from
      hf.dist_le_mul (γ U) y)).2
    have hc := hopfLax_le_cost hf ht x (γ U)
    rw [hy,hdp] at hc
    rw [hdq] at hLip
    have hc' : dist x y^2/(2*t)-(u*dist x y)^2/(2*t) ≤ (L:ℝ)*((1-u)*dist x y) := by
      linarith
    have he : dist x y^2-(u*dist x y)^2 ≤
        (L:ℝ)*((1-u)*dist x y)*(2*t) := by
      have hh := mul_le_mul_of_nonneg_right hc' (show 0 ≤ 2*t by positivity)
      field_simp at hh
      nlinarith [mul_le_mul_of_nonneg_right hh hr.le]
    have hpos : 0 < (1-u)*dist x y := mul_pos (by linarith) hr
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith
  have hc : Continuous (fun u : ℝ => dist x y*(1+u)) := by fun_prop
  have hbound : ∀ᶠ u : ℝ in 𝓝[<] 1, dist x y*(1+u) ≤ 2*t*(L:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))] with u hu hpos
    exact hparam u hpos.le hu
  have hl := le_of_tendsto ((hc.continuousAt (x := (1:ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio (1:ℝ)))) hbound
  linarith

 theorem hopfRadius_le_sharp [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {t : ℝ} (ht : 0 < t) (x : X) :
    hopfRadius f t x ≤ t*(L:ℝ) := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf ht x
  rw [he]
  exact hopfLax_minimizer_dist_sharp hf hgeo ht hy

 theorem hopfLax_slope_le_lipschitz [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {t : ℝ} (ht : 0 < t) (x : X) :
    localSlope (hopfLax f t) x ≤ (L : ℝ≥0∞) := by
  apply (hopfLax_slope_le hf ht x).trans
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ ht).mpr
  simpa only [mul_comm t] using hopfRadius_le_sharp hf hgeo ht x

theorem lipschitz_of_quadratic_cost (hgeo : IsGeodesicSpace X) {F : X → ℝ}
    (hF : Continuous F) {L C : ℝ} (hL : 0 ≤ L)
    (hcost : ∀ x z : X, F z-F x ≤ L*dist x z+C*dist x z^2) :
    LipschitzWith ⟨L,hL⟩ F := by
  have hdir : ∀ x z : X, F z-F x ≤ L*dist x z := by
    intro x z
    obtain ⟨γ,hγ0,hγ1,hγ⟩ := hgeo x z
    let c : ℝ → Time := projIcc 0 1 zero_le_one
    let g : ℝ → ℝ := fun u => F (γ (c u))
    have hc : Continuous c := continuous_projIcc
    have hg : Continuous g := hF.comp (γ.continuous.comp hc)
    have hdist : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
        dist (γ (c a)) (γ (c b)) = |a-b| *dist x z := by
      intro a b ha hb
      rw [hγ,hγ0,hγ1]
      simp only [c,projIcc_of_mem zero_le_one ha,projIcc_of_mem zero_le_one hb]
    have hg0 : g 0 = F x := by simp [g,c,hγ0]
    have hg1 : g 1 = F z := by simp [g,c,hγ1]
    have hbound := image_le_of_liminf_slope_right_le_deriv_boundary
      hg.continuousOn (B := fun u => F x+L*dist x z*u)
      (B' := fun _ => L*dist x z) (a := 0) (b := 1)
      (by simp [hg0]) (by fun_prop) (fun u _ => by
        simpa using ((hasDerivAt_id u).const_mul (L*dist x z)).const_add (F x)
          |>.hasDerivWithinAt)
    have hb : ∀ u ∈ Ico (0:ℝ) 1, ∀ r : ℝ, L*dist x z < r →
        ∃ᶠ v in 𝓝[>] u, slope g u v < r := by
      intro u hu r hr
      have hlim : Tendsto (fun v : ℝ => L*dist x z+C*dist x z^2*(v-u))
          (𝓝[>] u) (𝓝 (L*dist x z)) := by
        simpa using ((show Continuous (fun v : ℝ => L*dist x z+C*dist x z^2*(v-u)) by
          fun_prop).continuousAt (x := u)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi u))
      have hev : ∀ᶠ v in 𝓝[>] u, L*dist x z+C*dist x z^2*(v-u) < r :=
        hlim.eventually (Iio_mem_nhds hr)
      have hev' : ∀ᶠ v in 𝓝[>] u, v < 1 := nhdsWithin_le_nhds (Iio_mem_nhds hu.2)
      apply Filter.Eventually.frequently
      filter_upwards [hev,hev',self_mem_nhdsWithin] with v hv hv1 huv
      have hue : u ∈ Icc (0:ℝ) 1 := ⟨hu.1,hu.2.le⟩
      have hve : v ∈ Icc (0:ℝ) 1 := ⟨hu.1.trans (le_of_lt huv),hv1.le⟩
      have hd := hcost (γ (c u)) (γ (c v))
      rw [hdist u v hue hve,abs_sub_comm u v,abs_of_nonneg (sub_nonneg.mpr huv.le)] at hd
      have hs : slope g u v ≤ L*dist x z+C*dist x z^2*(v-u) := by
        rw [slope_def_field]
        apply (div_le_iff₀ (sub_pos.mpr huv)).mpr
        change g v-g u ≤ _ at hd
        dsimp [g] at *
        nlinarith
      exact hs.trans_lt hv
    have hh := hbound hb (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    rw [hg1] at hh
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x z
  change |F x-F z| ≤ L*dist x z
  apply abs_le.mpr
  have h₁ := hdir x z
  have h₂ := hdir z x
  rw [dist_comm z x] at h₂
  constructor <;> linarith

 
theorem hopfLax_lipschitz [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {t : ℝ} (ht : 0 < t) :
    LipschitzWith L (hopfLax f t) := by
  apply lipschitz_of_quadratic_cost hgeo (hopfLax_continuous hf ht) L.coe_nonneg
    (C := 1/(2*t))
  intro x z
  have h := hopfLax_difference_radius hf ht x z
  have hR : hopfRadius f t x/t ≤ (L:ℝ) := by
    apply (div_le_iff₀ ht).mpr
    simpa only [mul_comm t] using hopfRadius_le_sharp hf hgeo ht x
  have hh := mul_le_mul_of_nonneg_right hR (dist_nonneg (x := x) (y := z))
  calc
    _ ≤ (L:ℝ)*dist x z+dist x z^2/(2*t) := h.trans (add_le_add hh le_rfl)
    _ = _ := by ring

lemma quadratic_weighted_triangle {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    (a+b)^2/(2*(s+t)) ≤ a^2/(2*s)+b^2/(2*t) := by
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*s*t*(s+t))).mp
  have h₁ : ((a+b)^2/(2*(s+t)))*(2*s*t*(s+t)) = (a+b)^2*s*t := by
    field_simp
  have h₂ : (a^2/(2*s)+b^2/(2*t))*(2*s*t*(s+t)) =
      a^2*t*(s+t)+b^2*s*(s+t) := by field_simp
  rw [h₁,h₂]
  nlinarith [sq_nonneg (t*a-s*b)]

 
theorem hopfLax_semigroup [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : X) :
    hopfLax (hopfLax f t) s x = hopfLax f (s+t) x := by
  have hsum : 0 < s+t := add_pos hs ht
  have hQt := hopfLax_lipschitz hf hgeo ht
  apply le_antisymm
  · obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hf hsum x
    obtain ⟨γ,hγ0,hγ1,hγ⟩ := hgeo x y
    let u : Time := ⟨s/(s+t),by positivity,by
      apply (div_le_one hsum).mpr; linarith⟩
    let z := γ u
    have hdxz : dist x z = s/(s+t)*dist x y := by
      dsimp [z]
      rw [← hγ0,hγ]
      change |0-s/(s+t)| * dist (γ 0) (γ 1) = _
      rw [hγ0,hγ1,zero_sub,abs_neg,abs_of_pos (div_pos hs hsum)]
    have hdzy : dist z y = t/(s+t)*dist x y := by
      dsimp [z]
      rw [← hγ1,hγ]
      change |s/(s+t)-1| * dist (γ 0) (γ 1) = _
      rw [hγ0,hγ1,abs_of_nonpos (by
        have := (div_le_one hsum).mpr (show s ≤ s+t by linarith)
        linarith)]
      field_simp
      ring
    have hcost := hopfLax_le_cost hQt hs x z
    have hfz := hopfLax_le_cost hf ht z y
    have he : (t/(s+t)*dist x y)^2/(2*t)+(s/(s+t)*dist x y)^2/(2*s) =
        dist x y^2/(2*(s+t)) := by
      field_simp
      ring
    rw [hdxz] at hcost
    rw [hy]
    rw [hdzy] at hfz
    linarith
  · obtain ⟨z,hz,_⟩ := hopfLax_exists_minimizer hQt hs x
    obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hf ht z
    have hc := hopfLax_le_cost hf hsum x y
    have htri : dist x y^2/(2*(s+t)) ≤ (dist x z+dist z y)^2/(2*(s+t)) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ dist_nonneg (dist_triangle x z y) 2)
        (by positivity)
    have hquad := quadratic_weighted_triangle hs ht (dist x z) (dist z y)
    rw [hz,hy]
    linarith

 
theorem hopfLax_time_difference_sharp [ProperSpace X] {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : X) :
    |hopfLax f t x-hopfLax f s x| ≤ (L:ℝ)^2/2 * |t-s| := by
  have hdir : ∀ s t : ℝ, 0 < s → s < t →
      0 ≤ hopfLax f s x-hopfLax f t x ∧
      hopfLax f s x-hopfLax f t x ≤ (t-s)*(L:ℝ)^2/2 := by
    intro u v hu huv
    have hvu : 0 < v-u := sub_pos.mpr huv
    have he := hopfLax_semigroup hf hgeo hvu hu x
    rw [sub_add_cancel] at he
    have hb := hopfLax_bounds (hopfLax_lipschitz hf hgeo hu) hvu x
    rw [he] at hb
    constructor <;> linarith [hb.1,hb.2]
  rcases lt_trichotomy s t with h | rfl | h
  · have hh := hdir s t hs h
    rw [abs_of_nonpos (by linarith : hopfLax f t x-hopfLax f s x ≤ 0),
      abs_of_pos (sub_pos.mpr h)]
    nlinarith [hh.2]
  · simp
  · have hh := hdir t s ht h
    rw [abs_of_nonneg hh.1,abs_of_neg (sub_neg.mpr h)]
    nlinarith [hh.2]

 
theorem hopfLax_tendsto_zero {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    Tendsto (fun t : ℝ => hopfLax f t x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hlow : Tendsto (fun t : ℝ => f x-t*(L:ℝ)^2/2) (𝓝[>] 0) (𝓝 (f x)) := by
    simpa using ((show Continuous (fun t : ℝ => f x-t*(L:ℝ)^2/2) by fun_prop).continuousAt
      (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hopfLax_bounds hf ht x).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hopfLax_bounds hf ht x).2

end RegularPointCoordinates

end OAI

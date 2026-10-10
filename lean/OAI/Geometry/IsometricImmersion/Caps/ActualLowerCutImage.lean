import OAI.Geometry.IsometricImmersion.Caps.ActualPulseCapSeparation

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem actual_flow_preimage_near_center
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    {t y : ℝ} (ht : |t| ≤ 1) (hy : |y| ≤ 3/4) :
    ∃ s ∈ Ioo (-1 : ℝ) 1, Y s t = y := by
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hnegp : boxPoint t (-1) ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (-1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hposp : boxPoint t 1 ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hneg : |Y (-1) t+1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t (-1)) hnegp
  have hpos : |Y 1 t-1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t 1) hposp
  have hlo : Y (-1) t < y := by linarith [(abs_le.mp hneg).2,(abs_le.mp hy).1]
  have hhi : y < Y 1 t := by linarith [(abs_le.mp hpos).1,(abs_le.mp hy).2]
  have hmap : MapsTo (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,⟨ht2.1.le,ht2.2.le⟩⟩
  have hcont : ContinuousOn (fun s : ℝ => Y s t) (Icc (-1 : ℝ) 1) :=
    hf.continuous.comp (by fun_prop : ContinuousOn (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)) hmap
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont ⟨hlo.le,hhi.le⟩
  refine ⟨s,⟨?_,?_⟩,hse⟩
  · by_contra hn
    have he : s = -1 := le_antisymm (le_of_not_gt hn) hs.1
    subst s
    linarith
  · by_contra hn
    have he : s = 1 := le_antisymm hs.2 (le_of_not_gt hn)
    subst s
    linarith

def lowerCutRectangle (L r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) : LowerCapRectangle (-r/2) where
  left := -(2*L*r)
  right := 2*L*r
  bottom := -(3*r/2)
  top := -(3*r/4)
  left_gt := by nlinarith
  right_lt := by nlinarith
  bottom_gt := by linarith
  horizontal := by nlinarith [mul_pos hL hr]
  vertical := by linarith
  top_lt := by linarith
  ceiling_le := by linarith

theorem actual_lower_cut_in_cap_image
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa q0 L r : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    {t : ℝ} (ht : |t| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint t (-r)) ∈ (lowerCutRectangle L r hL hr hrhalf hLr).image Y := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (p : Coord) (hp : p ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) p| ≤ M := hf.quotientBound [i] (by norm_num) p hp
  have hTpos : 0 < L*r := mul_pos hL hr
  have ht1 : |t| ≤ 1 := ht.trans (by linarith)
  have hqt : |q0*t| ≤ (1/20)*(L*r) := by
    rw [abs_mul]
    exact mul_le_mul hq0 ht (abs_nonneg _) (by norm_num)
  have hy : |-r-q0*t| ≤ 3/4 := by
    have h := abs_sub (-r) (q0*t)
    rw [abs_neg,abs_of_pos hr] at h
    linarith
  obtain ⟨s,hs,hse⟩ := actual_flow_preimage_near_center hf ht1 hy
  have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have htt : t ∈ Icc (-(L*r)) (L*r) := abs_le.mp ht
  have htheta : |Y s t+q0*t| ≤ r := by
    rw [hse]
    have he : -r-q0*t+q0*t = -r := by ring
    rw [he,abs_neg,abs_of_pos hr]
  have hclose := flow_segment_quotient_near_center hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hpartial hq0 hcenter
    hTpos (by linarith : L*r < 2) hs2 htt htheta hrsmall
  have hdist := actual_shear_seed_distance hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hTpos (by linarith : L*r < 2) hs2 htt hclose
  have hdist' : |-r-s| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      rw [div_mul_eq_mul_div₀, one_mul, mul_comm (10 : ℝ) L, mul_div_mul_left _ _ hL.ne']
    have hbound := hdist.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq he)
    simpa only [hse,sub_add_cancel] using hbound
  refine ⟨boxPoint t s,?_,?_⟩
  · change (boxPoint t s) ∈ closedRectangle (-(2*L*r)) (2*L*r) (-(3*r/2)) (-(3*r/4))
    constructor
    · simpa [boxPoint] using (show t ∈ Icc (-(2*L*r)) (2*L*r) by
        constructor <;> nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2])
    · simpa [boxPoint] using (show s ∈ Icc (-(3*r/2)) (-(3*r/4)) by
        constructor <;> linarith [(abs_le.mp hdist').1,(abs_le.mp hdist').2])
  · ext i
    fin_cases i <;> simp [capChart,capFlowHeight,coordinatePoint,boxPoint,inverseShearCoordinates,hse]

end SmoothLocal.Pulse

end

end OAI

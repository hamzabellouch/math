import OAI.Geometry.RCD.Harmonic.InteriorQuadraticDefect

namespace OAI

/-! # Recovering the full midpoint law from interior time intervals -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem quadratic_midpoint_error_bound (f₀ f₁ fa fb fm c C δ ε : ℝ)
    (hδ0 : 0≤δ) (hδ1 : δ≤1) (hc0 : 0≤c) (hc : c≤C)
    (ha : |fa-f₀|≤ε) (hb : |fb-f₁|≤ε) :
    |fm-(f₀+f₁)/2+c/8|≤|fm-(fa+fb)/2+c*(1-2*δ)^2/8|+ε+C*δ/2 := by
  let I := fm-(fa+fb)/2+c*(1-2*δ)^2/8
  have he : fm-(f₀+f₁)/2+c/8=I+((fa-f₀)+(fb-f₁))/2+c*δ*(1-δ)/2 := by
    dsimp only [I]
    ring
  have heps : |((fa-f₀)+(fb-f₁))/2|≤ε := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := (abs_add_le (fa-f₀) (fb-f₁)).trans (add_le_add ha hb)
    linarith
  have hcurv0 : 0≤c*δ*(1-δ)/2 := by positivity
  have hcurv : c*δ*(1-δ)/2≤C*δ/2 := by
    have h1 : c*δ*(1-δ)≤c*δ := mul_le_of_le_one_right (mul_nonneg hc0 hδ0) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right hc hδ0
    linarith
  rw [he]
  calc
    _ ≤ |I|+|((fa-f₀)+(fb-f₁))/2|+|c*δ*(1-δ)/2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by rw [abs_of_nonneg hcurv0]; linarith

variable {X : Type*} [MetricSpace X]

abbrev quadraticMidpointTime : Time := ⟨1/2,by norm_num⟩

theorem squared_distance_along_geodesic (γ : C(Time,X)) (hg : IsGeodesic γ)
    (z : X) {R : ℝ} (hR : 0≤R) (h0 : dist z (γ 0)≤R) (h1 : dist z (γ 1)≤R)
    (s t : Time) :
    |dist z (γ s)^2/2-dist z (γ t)^2/2|≤6*R^2*|(s:ℝ)-t| := by
  have hd : dist (γ 0) (γ 1)≤2*R := by
    have hh := dist_triangle (γ 0) z (γ 1)
    rw [dist_comm (γ 0) z] at hh
    linarith
  have hstay (u : Time) : dist z (γ u)≤3*R := by
    have hh := hg 0 u
    have hdist : dist (γ 0) (γ u)≤2*R := by
      rw [hh]
      have hu : |(0:Time)-(u:ℝ)|≤1 := by
        change |(0:ℝ)-(u:ℝ)|≤1
        rw [zero_sub,abs_neg,abs_of_nonneg u.property.1]
        exact u.property.2
      exact (mul_le_mul hu hd dist_nonneg zero_le_one).trans_eq (one_mul _)
    linarith [dist_triangle z (γ 0) (γ u)]
  have hdiff : |dist z (γ s)-dist z (γ t)|≤|(s:ℝ)-t| *(2*R) := by
    calc
      _ ≤ dist (γ s) (γ t) := by simpa only [dist_comm] using abs_dist_sub_le (γ s) (γ t) z
      _ = |(s:ℝ)-t| *dist (γ 0) (γ 1) := hg s t
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  have hsum : (dist z (γ s)+dist z (γ t))/2≤3*R := by linarith [hstay s,hstay t]
  rw [show dist z (γ s)^2/2-dist z (γ t)^2/2=
    (dist z (γ s)-dist z (γ t))*((dist z (γ s)+dist z (γ t))/2) by ring,
    abs_mul,abs_of_nonneg (by positivity : 0≤(dist z (γ s)+dist z (γ t))/2)]
  exact (mul_le_mul hdiff hsum (by positivity) (by positivity)).trans_eq (by ring)

def fullMidpointDefect (z : X) (γ : C(Time,X)) : ℝ :=
  dist z (γ quadraticMidpointTime)^2/2-(dist z (γ 0)^2/2+dist z (γ 1)^2/2)/2+
    dist (γ 0) (γ 1)^2/8

theorem fullMidpointDefect_le_interior (γ : C(Time,X)) (hg : IsGeodesic γ)
    (z : X) {R δ : ℝ} (hR : 0≤R) (h0 : dist z (γ 0)≤R) (h1 : dist z (γ 1)≤R)
    (hδ0 : 0<δ) (hδ1 : δ<1/2) (a b : Time) (ha : (a:ℝ)=δ) (hb : (b:ℝ)=1-δ) :
    |fullMidpointDefect z γ|≤|interiorQuadraticDefect (fun x => dist z x^2/2) a b quadraticMidpointTime γ|+
      8*R^2*δ := by
  have hα := squared_distance_along_geodesic γ hg z hR h0 h1 a 0
  have hβ := squared_distance_along_geodesic γ hg z hR h0 h1 b 1
  rw [ha] at hα
  rw [hb] at hβ
  change |dist z (γ a)^2/2-dist z (γ 0)^2/2|≤6*R^2*|δ-0| at hα
  have hα' : |dist z (γ a)^2/2-dist z (γ 0)^2/2|≤6*R^2*δ := by
    simpa only [sub_zero,abs_of_pos hδ0] using hα
  change |dist z (γ b)^2/2-dist z (γ 1)^2/2|≤6*R^2*|(1-δ)-1| at hβ
  have heβ : |(1-δ)-1|=δ := by rw [show (1-δ)-1= -δ by ring,abs_neg,abs_of_pos hδ0]
  rw [heβ] at hβ
  have hd : dist (γ 0) (γ 1)≤2*R := by
    have hh := dist_triangle (γ 0) z (γ 1)
    rw [dist_comm (γ 0) z] at hh
    linarith
  have hcost : dist (γ 0) (γ 1)^2≤4*R^2 := by nlinarith [dist_nonneg (x:=γ 0) (y:=γ 1)]
  have hestimate := quadratic_midpoint_error_bound
    (dist z (γ 0)^2/2) (dist z (γ 1)^2/2) (dist z (γ a)^2/2)
    (dist z (γ b)^2/2) (dist z (γ quadraticMidpointTime)^2/2) (dist (γ 0) (γ 1)^2)
    (4*R^2) δ (6*R^2*δ) hδ0.le (by linarith) (sq_nonneg _) hcost hα' hβ
  have hI : interiorQuadraticDefect (fun x => dist z x^2/2) a b quadraticMidpointTime γ=
      dist z (γ quadraticMidpointTime)^2/2-(dist z (γ a)^2/2+dist z (γ b)^2/2)/2+
        dist (γ 0) (γ 1)^2*(1-2*δ)^2/8 := by
    dsimp only [interiorQuadraticDefect,quadraticMidpointTime]
    rw [ha,hb]
    field_simp [show 1-δ-δ≠0 by linarith]
    ring
  change |fullMidpointDefect z γ|≤_ at hestimate
  rw [← hI] at hestimate
  convert hestimate using 1
  ring

end RegularPointCoordinates

end

end OAI

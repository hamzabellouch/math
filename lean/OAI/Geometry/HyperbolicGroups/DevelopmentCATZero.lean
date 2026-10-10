import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

theorem catZero_of_localCN_radial (g : IsGeodesic X) (hb : RadialBusemann X)
    (hl : ∀ m : X, ∃ r : ℝ, 0<r ∧ ∀ a b z : X,
      a ∈ Metric.ball m r → b ∈ Metric.ball m r → z ∈ Metric.ball m r →
      dist a m=dist a b/2 → dist m b=dist a b/2 →
      dist z m^2≤(dist z a^2+dist z b^2)/2-dist a b^2/4) : CATZero X := by
  apply catZero_of_segment_midpoint g
  intro γ x y hγ z
  let m := γ (1/2)
  obtain ⟨r,hr,hcat⟩ := hl m
  let α : ℝ → X := fun u => γ ((1-u)*(1/2)+u*0)
  let β : ℝ → X := fun u => γ ((1-u)*(1/2)+u*1)
  have hα : IsSegment α m x := by simpa [α,m,hγ.1] using hγ.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hβ : IsSegment β m y := by simpa [β,m,hγ.2.1] using hγ.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
  obtain ⟨δ,hδ⟩ := g m z
  have hmx : dist m x=dist x y/2 := by
    have hh := hγ.2.2 (1/2) (by norm_num) 0 (by norm_num)
    simpa [m,hγ.1,div_eq_mul_inv,mul_comm] using hh
  have hmy : dist m y=dist x y/2 := by
    have hh := hγ.2.2 (1/2) (by norm_num) 1 (by norm_num)
    norm_num at hh
    simpa [m,hγ.2.1,div_eq_mul_inv,mul_comm] using hh
  let R : ℝ := 1+dist x y+dist m z
  have hR : 0<R := by dsimp [R]; linarith [dist_nonneg (x:=x) (y:=y),dist_nonneg (x:=m) (y:=z)]
  let t : ℝ := min (1/2) (r/(2*R))
  have ht0 : 0<t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have ht : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le,ht1⟩
  have htR : t*R≤r/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*R)).mp (min_le_right (1/2:ℝ) (r/(2*R)))
    change t*(2*R)≤r at hh
    linarith
  have hdx : dist m (α t)=t*dist x y/2 := by rw [hα.dist_from_source ht,hmx]; ring
  have hdy : dist m (β t)=t*dist x y/2 := by rw [hβ.dist_from_source ht,hmy]; ring
  have hdz : dist m (δ t)=t*dist m z := hδ.dist_from_source ht
  have hxy : dist (α t) (β t)=t*dist x y := by
    have htlo : (1-t)*(1/2)+t*0 ∈ Icc (0:ℝ) 1 := ⟨by nlinarith [ht.2],by nlinarith [ht.1]⟩
    have hthi : (1-t)*(1/2)+t*1 ∈ Icc (0:ℝ) 1 := ⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩
    dsimp [α,β]
    rw [hγ.2.2 _ htlo _ hthi,show (1-t)*(1/2)+t*0-((1-t)*(1/2)+t*1) = -t by ring,
      abs_neg,abs_of_nonneg ht0.le]
  have ha : α t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdx]
    have hh : dist x y≤R := by dsimp [R]; linarith [dist_nonneg (x:=m) (y:=z)]
    nlinarith [mul_le_mul_of_nonneg_left hh ht0.le,dist_nonneg (x:=x) (y:=y)]
  have hc : β t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdy]
    have hh : dist x y≤R := by dsimp [R]; linarith [dist_nonneg (x:=m) (y:=z)]
    nlinarith [mul_le_mul_of_nonneg_left hh ht0.le,dist_nonneg (x:=x) (y:=y)]
  have hz : δ t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdz]
    have hh : dist m z≤R := by dsimp [R]; linarith [dist_nonneg (x:=x) (y:=y)]
    linarith [mul_le_mul_of_nonneg_left hh ht0.le]
  have hcn := hcat (α t) (β t) (δ t) ha hc hz
    (by rw [dist_comm,hdx,hxy]) (by rw [hdy,hxy])
  rw [dist_comm (δ t) m,hdz,hxy] at hcn
  have hxa := hb m z x δ α hδ hα t ht
  have hya := hb m z y δ β hδ hβ t ht
  have hx2 := (sq_le_sq₀ (dist_nonneg (x:=δ t) (y:=α t)) (by positivity)).mpr hxa
  have hy2 := (sq_le_sq₀ (dist_nonneg (x:=δ t) (y:=β t)) (by positivity)).mpr hya
  have hres : t^2*(dist m z^2-((dist z x^2+dist z y^2)/2-dist x y^2/4))≤0 := by
    nlinarith
  have hh : dist m z^2-((dist z x^2+dist z y^2)/2-dist x y^2/4)≤0 := by
    by_contra! hpos
    exact (not_lt_of_ge hres) (mul_pos (sq_pos_of_pos ht0) hpos)
  dsimp [m] at hh
  rw [dist_comm (γ (1/2)) z] at hh
  linarith



end HyperbolicObstruction
end
end

end OAI

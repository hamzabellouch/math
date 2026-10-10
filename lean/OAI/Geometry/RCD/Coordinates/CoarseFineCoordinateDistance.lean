import OAI.Geometry.RCD.Coordinates.FullScaleCoordinateDistance

namespace OAI

/-! # Global distance control from a coarse chart and fine local charts -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- The coarse approximation controls widely separated points. The
all-scale charts control the remaining pairs, with the same small error. -/
theorem coarse_fine_coordinate_distance {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {v : X → Euclidean n} {U : Set X} {r S T ε η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (herror : ε*r ≤ η*T)
    (hU : ∀ x ∈ U, dist x p ≤ S*r)
    (hcoarse : IsPointedApproximation p 0 r S ε (fun z => r⁻¹ • (v z-v p)))
    (hfine : ∀ x ∈ U, ∀ s : ℝ, 0 < s → s < T →
      IsPointedApproximation x 0 s (1/16) η (fun z => s⁻¹ • (v z-v x))) :
    ∀ x ∈ U, ∀ y ∈ U,
      (1-32*η)*dist x y ≤ dist (v x) (v y) ∧
        dist (v x) (v y) ≤ (1+32*η)*dist x y := by
  intro x hx y hy
  by_cases hxy : dist x y < T/32
  · have hT : 0 < T/32 := lt_of_le_of_lt dist_nonneg hxy
    exact full_scale_coordinate_distance
      (U := {x,y}) (by
        intro a ha b hb
        change a=x ∨ a=y at ha
        change b=x ∨ b=y at hb
        rcases ha with hax | hay <;> rcases hb with hbx | hby
        · simpa only [hax,hbx,dist_self] using hT
        · simpa only [hax,hby] using hxy
        · simpa only [hay,hbx,dist_comm y x] using hxy
        · simpa only [hay,hby,dist_self] using hT)
      (by
        intro a ha s hs hsT
        change a=x ∨ a=y at ha
        rcases ha with hax | hay
        · rw [hax]; exact hfine x hx s hs hsT
        · rw [hay]; exact hfine y hy s hs hsT)
      x (by simp) y (by simp)
  · have hfar : T ≤ 32*dist x y := by linarith only [hxy]
    have hh := hcoarse.2.1 x y (hU x hx) (hU y hy)
    rw [dist_smul₀,Real.norm_of_nonneg (inv_pos.mpr hr).le,dist_sub_right] at hh
    have hscaled : |dist (v x) (v y)-dist x y| ≤ r*ε := by
      have heq : r*(r⁻¹*dist (v x) (v y)-dist x y/r)=
          dist (v x) (v y)-dist x y := by field_simp
      rw [← heq,abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hh hr.le
    have hefar := mul_le_mul_of_nonneg_left hfar hη
    have hb := abs_le.mp hscaled
    constructor <;> nlinarith only [hb.1,hb.2,herror,hefar]

theorem coarse_fine_coordinate_lipschitz {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {v : X → Euclidean n} {U : Set X} {r S T ε η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (herror : ε*r ≤ η*T)
    (hU : ∀ x ∈ U, dist x p ≤ S*r)
    (hcoarse : IsPointedApproximation p 0 r S ε (fun z => r⁻¹ • (v z-v p)))
    (hfine : ∀ x ∈ U, ∀ s : ℝ, 0 < s → s < T →
      IsPointedApproximation x 0 s (1/16) η (fun z => s⁻¹ • (v z-v x))) :
    LipschitzOnWith ⟨1+32*η,by positivity⟩ v U :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
    (coarse_fine_coordinate_distance hr hη herror hU hcoarse hfine x hx y hy).2

end RegularPointCoordinates

end

end OAI

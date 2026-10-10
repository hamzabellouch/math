import OAI.Geometry.RCD.Transport.QuadraticMidpointError

namespace OAI

/-! # Metric algebra of the local quadratic midpoints used for rigidity -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y]

structure LocalQuadraticMidpointGeometry (q : Y) where
  mid : ball q (1/2:ℝ) → ball q (1/2:ℝ) → ball q (1/2:ℝ)
  left : ∀ (x y : ball q (1/2:ℝ)), dist (x:Y) (mid x y:Y) = dist (x:Y) (y:Y)/2
  right : ∀ (x y : ball q (1/2:ℝ)), dist (mid x y:Y) (y:Y) = dist (x:Y) (y:Y)/2
  quadratic : ∀ (x y : ball q (1/2:ℝ)), ∀ z ∈ ball q (1:ℝ),
    dist z (mid x y:Y)^2 = (dist z (x:Y)^2+dist z (y:Y)^2)/2-dist (x:Y) (y:Y)^2/4

namespace LocalQuadraticMidpointGeometry
variable {q : Y} (G : LocalQuadraticMidpointGeometry q)

private theorem mem_large (x : ball q (1/2:ℝ)) : (x:Y) ∈ ball q (1:ℝ) :=
  x.property.trans (by norm_num : (1/2:ℝ) < 1)

theorem unique (x y c : ball q (1/2:ℝ))
    (hleft : dist (x:Y) (c:Y) = dist (x:Y) (y:Y)/2)
    (hright : dist (c:Y) (y:Y) = dist (x:Y) (y:Y)/2) : c = G.mid x y := by
  apply Subtype.ext
  apply dist_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [G.quadratic x y c (mem_large c),dist_comm (c:Y) (x:Y),hleft,hright]
  ring

@[simp] theorem mid_self (x : ball q (1/2:ℝ)) : G.mid x x = x := by
  symm
  apply G.unique <;> simp

theorem mid_comm (x y : ball q (1/2:ℝ)) : G.mid x y = G.mid y x := by
  apply G.unique
  · rw [dist_comm (y:Y),G.right,dist_comm (y:Y) (x:Y)]
  · rw [dist_comm _ (x:Y),G.left,dist_comm (y:Y) (x:Y)]

theorem half_distance (p x y : ball q (1/2:ℝ)) :
    dist (G.mid p x:Y) (G.mid p y:Y) = dist (x:Y) (y:Y)/2 := by
  have h₁ := G.quadratic p x (G.mid p y) (mem_large (G.mid p y))
  have h₂ := G.quadratic p y x (mem_large x)
  rw [dist_comm (G.mid p y:Y) (p:Y),G.left] at h₁
  rw [dist_comm (G.mid p y:Y) (x:Y),h₂] at h₁
  rw [dist_comm (x:Y) (p:Y)] at h₁
  rw [dist_comm (G.mid p y:Y) (G.mid p x:Y)] at h₁
  apply (sq_eq_sq₀ dist_nonneg (div_nonneg dist_nonneg (by norm_num))).mp
  nlinarith only [h₁]

theorem mid_distance_le (x y x' y' : ball q (1/2:ℝ)) :
    dist (G.mid x y:Y) (G.mid x' y':Y) ≤ (dist (x:Y) (x':Y)+dist (y:Y) (y':Y))/2 := by
  calc
    _ ≤ dist (G.mid x y:Y) (G.mid x y':Y)+dist (G.mid x y':Y) (G.mid x' y':Y) := dist_triangle _ _ _
    _ = dist (y:Y) (y':Y)/2+dist (x:Y) (x':Y)/2 := by
      rw [G.half_distance,G.mid_comm x y',G.mid_comm x' y',G.half_distance]
    _ = _ := by ring

end LocalQuadraticMidpointGeometry
end RegularPointCoordinates

end

end OAI

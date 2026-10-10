import OAI.MeasureTheory.Falconer.Radial.RadialSphereLaw

namespace OAI

/-! # The sphere law has exactly the original directional cap and plate bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem originalRadialSphereLaw_ball (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Sphere d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z (Metric.ball w r) =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z (Metric.ball w r) measurableSet_ball]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [mem_ofPred_eq,hx,true_and,Metric.mem_ball,Subtype.dist_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

theorem originalRadialSphereLaw_slab (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Space d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z {u : Sphere d | |inner ℝ w (u:Space d)| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ w (normalize (x-z))| ≤ r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z _
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [hx,true_and,mem_ofPred_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

end Falconer

end OAI

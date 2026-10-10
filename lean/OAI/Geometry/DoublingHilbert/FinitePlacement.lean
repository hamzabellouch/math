import Mathlib
import OAI.Geometry.DoublingHilbert.SparseCoordinates
import OAI.Geometry.DoublingHilbert.CoordinateSupport
import OAI.Geometry.DoublingHilbert.Auerbach
import OAI.Geometry.DoublingHilbert.CoordinateMap
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem dist_point_le_of_coordinate_bound (p q : Base) (w w' : Tuple) {R : ℝ}
    (hR : 0 ≤ R) (hc : ∀ i, |point p w i - point q w' i| ≤ R) :
    dist (point p w) (point q w') ≤ 6 * R := by
  have hf : |p.1 - q.1| ≤ R := by simpa using hc 0
  have hs : |p.2 - q.2| ≤ R := by simpa using hc 1
  have hw : ∀ j, w j ≠ w' j → scale j ≤ R := by
    intro j hj
    obtain ⟨i, hi⟩ := exists_coordinate_difference (p := p) (q := q) hj
    exact hi ▸ hc i
  have ht := norm_map_point_sub_le (LinearMap.id : RealL2 →ₗ[ℝ] RealL2)
    (fun i a => by simp only [LinearMap.id_apply,
      lp.norm_single (by norm_num : (0 : ENNReal) < 2), Real.norm_eq_abs]; rfl)
    p q w w' hR hf hs hw
  simpa only [LinearMap.id_apply, dist_eq_norm] using ht

                                                                                   
                                                                               
                                                                         
theorem finite_placement {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hB : ¬ FiniteDimensional ℝ B) (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ T : RealL2 →ₗ[ℝ] B, ∀ x ∈ X, ∀ y ∈ X,
       dist x y / 6 ≤ dist (T x) (T y) ∧ dist (T x) (T y) ≤ 6 * dist x y := by
  classical
  obtain ⟨I, hI⟩ := finite_coordinate_support X hX
  obtain ⟨v, hv, hvc⟩ := exists_auerbach_vectors (ι := I) hB
  let T := coordinateMap I v
  have hT : ∀ i a, ‖T (lp.single 2 i a)‖ ≤ |a| := coordinateMap_single I v hv
  refine ⟨T, ?_⟩
  intro x hx y hy
  have hcoords : ∀ i, |(x - y) i| ≤ ‖T (x - y)‖ :=
    coordinateMap_lower I v hvc (x - y) (by
      intro i hi
      change x i - y i = 0
      rw [hI x hx i hi, hI y hy i hi, sub_self])
  obtain ⟨p, w, _, rfl⟩ := hX x hx
  obtain ⟨q, w', _, rfl⟩ := hX y hy
  have hlow := dist_point_le_of_coordinate_bound p q w w' (norm_nonneg (T _)) hcoords
  have hupp := norm_map_point_sub_le_dist T hT p q w w'
  rw [map_sub, ← dist_eq_norm] at hlow hupp
  constructor
  · linarith
  · exact hupp

end CompactBanach
end

end OAI

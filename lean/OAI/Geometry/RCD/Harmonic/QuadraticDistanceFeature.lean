import OAI.Geometry.RCD.Transport.QuadraticGeodesicGeometry

namespace OAI

/-! # Linear features from quadratic squared distances

Polarization about a fixed point embeds the space into real functions.
The exact squared-distance law makes every geodesic affine in these
functions. No inner-product or Euclidean structure is presumed.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def quadraticDistanceFeature (p x : X) : X → ℝ := fun z =>
  (dist p x^2+dist p z^2-dist x z^2)/2

@[simp] theorem quadraticDistanceFeature_self (p : X) : quadraticDistanceFeature p p=0 := by
  funext z
  simp [quadraticDistanceFeature]

@[simp] theorem quadraticDistanceFeature_diag (p x : X) :
    quadraticDistanceFeature p x x=dist p x^2 := by
  simp only [quadraticDistanceFeature,dist_self,zero_pow (by norm_num : 2≠0),sub_zero]
  ring

theorem quadraticDistanceFeature_symm (p x y : X) :
    quadraticDistanceFeature p x y=quadraticDistanceFeature p y x := by
  dsimp [quadraticDistanceFeature]
  rw [dist_comm y x]
  ring

theorem quadraticDistanceFeature_injective (p : X) :
    Function.Injective (quadraticDistanceFeature p) := by
  intro x y h
  have hx := congrFun h x
  have hy := congrFun h y
  simp only [quadraticDistanceFeature,dist_self,zero_pow (by norm_num : 2≠0),sub_zero] at hx hy
  rw [dist_comm y x] at hx
  have hz : dist x y^2=0 := by nlinarith only [hx,hy]
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hz)

namespace QuadraticGeodesicGeometry
variable (G : QuadraticGeodesicGeometry X)

theorem feature_path (p x y : X) (t : Time) :
    quadraticDistanceFeature p (G.path x y t) =
      (1-(t:ℝ)) • quadraticDistanceFeature p x+(t:ℝ) • quadraticDistanceFeature p y := by
  funext z
  have hp := G.quadratic x y p t
  have hz := G.quadratic x y z t
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,quadraticDistanceFeature]
  rw [dist_comm (G.path x y t) z,dist_comm x z,dist_comm y z]
  rw [hp,hz]
  ring

theorem feature_radial (p x : X) (t : Time) :
    quadraticDistanceFeature p (G.radial p t x)=(t:ℝ) • quadraticDistanceFeature p x := by
  simpa only [radial,quadraticDistanceFeature_self,smul_zero,zero_add] using
    G.feature_path p p x t

end QuadraticGeodesicGeometry
end RegularPointCoordinates

end

end OAI

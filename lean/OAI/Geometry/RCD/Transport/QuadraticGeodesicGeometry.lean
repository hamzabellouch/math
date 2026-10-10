import OAI.Geometry.RCD.Transport.QuadraticGeodesicUniqueness
import OAI.Analysis.RCDHeat.CompressionIntegral

namespace OAI

/-! # Metric operations supplied by exact quadratic geodesics

Exact quadratic distance identities determine unique geodesics and
radial similarities, including their composition and reversal laws.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable (X : Type*) [MetricSpace X]

structure QuadraticGeodesicGeometry where
  path : X → X → C(Time,X)
  geodesic : ∀ x y, IsGeodesic (path x y)
  initial : ∀ x y, path x y 0=x
  terminal : ∀ x y, path x y 1=y
  quadratic : ∀ x y z (t : Time), dist z (path x y t)^2 =
    (1-(t:ℝ))*dist z x^2+(t:ℝ)*dist z y^2-(t:ℝ)*(1-(t:ℝ))*dist x y^2

namespace QuadraticGeodesicGeometry
variable {X} (G : QuadraticGeodesicGeometry X)

theorem unique (x y : X) (γ : C(Time,X)) (hg : IsGeodesic γ)
    (h0 : γ 0=x) (h1 : γ 1=y) : γ=G.path x y := by
  apply quadratic_geodesic_unique (G.path x y) γ hg
    (h0.trans (G.initial x y).symm) (h1.trans (G.terminal x y).symm)
  simpa only [G.initial,G.terminal] using G.quadratic x y

def radial (p : X) (t : Time) (x : X) : X := G.path p x t

@[simp] theorem radial_zero (p x : X) : G.radial p 0 x=p := G.initial p x
@[simp] theorem radial_one (p x : X) : G.radial p 1 x=x := G.terminal p x

theorem dist_radial (p x y : X) (t : Time) :
    dist (G.radial p t x) (G.radial p t y)=(t:ℝ)*dist x y := by
  have he := quadratic_radial_distance (G.path p x) (G.path p y) (G.geodesic p y)
    ((G.initial p x).trans (G.initial p y).symm)
    (by simpa only [G.initial,G.terminal] using G.quadratic p x)
    (by simpa only [G.initial,G.terminal] using G.quadratic p y) t
  simpa only [radial,G.terminal] using he

theorem radial_lipschitz (p : X) (t : Time) :
    LipschitzWith ⟨t,t.property.1⟩ (G.radial p t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (G.dist_radial p x y t).le

theorem radial_antilipschitz (p : X) (t : Time) (ht : 0<(t:ℝ)) :
    AntilipschitzWith ⟨(t:ℝ)⁻¹,inv_nonneg.mpr ht.le⟩ (G.radial p t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  rw [G.dist_radial]
  change dist x y ≤ (t:ℝ)⁻¹*((t:ℝ)*dist x y)
  rw [← mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]

@[simp] theorem radial_self (p : X) (t : Time) : G.radial p t p=p := by
  have hh := G.geodesic p p t 0
  rw [G.initial,G.terminal,dist_self,mul_zero] at hh
  exact dist_eq_zero.mp hh

theorem radial_comp (p x : X) (s t : Time) :
    G.radial p s (G.radial p t x) =
      G.radial p ⟨(s:ℝ)*(t:ℝ),mul_nonneg s.property.1 t.property.1,
        (mul_le_mul_of_nonneg_right s.property.2 t.property.1).trans (by simpa using t.property.2)⟩ x := by
  have he := G.unique p (G.radial p t x) (subpath 0 t (G.path p x))
    ((G.geodesic p x).subpath 0 t)
    (by simp only [subpath_zero,G.initial]) (by simp only [subpath_one,radial])
  have hh := congrArg (fun γ : C(Time,X) => γ s) he
  change G.path p x (timeSegment 0 t s)=G.radial p s (G.radial p t x) at hh
  rw [← hh]
  congr 1
  apply Subtype.ext
  change (1-(s:ℝ))*0+(s:ℝ)*(t:ℝ)=(s:ℝ)*(t:ℝ)
  ring

theorem reverse_path (x y : X) (t : Time) :
    G.path x y (timeSegment 1 0 t)=G.path y x t := by
  have he := G.unique y x (subpath 1 0 (G.path x y))
    ((G.geodesic x y).subpath 1 0)
    (by simp only [subpath_zero,G.terminal]) (by simp only [subpath_one,G.initial])
  exact congrArg (fun γ : C(Time,X) => γ t) he

end QuadraticGeodesicGeometry
end RegularPointCoordinates

end

end OAI

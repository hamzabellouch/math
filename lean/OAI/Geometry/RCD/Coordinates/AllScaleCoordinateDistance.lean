import OAI.Geometry.RCD.Coordinates.NormalizedHausdorffImage

namespace OAI

/-! # From all smaller coordinate approximations to distance and image bounds -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] {n : ℕ}

theorem all_scale_coordinate_distance {u : X → Euclidean n} {U : Set X} {R η : ℝ}
    (hsmall : ∀ x ∈ U, ∀ y ∈ U, dist x y < R/4)
    (happ : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation x 0 r (1/2) η (fun z => r⁻¹ • (u z-u x))) :
    ∀ x ∈ U, ∀ y ∈ U,
      (1-4*η)*dist x y ≤ dist (u x) (u y) ∧
        dist (u x) (u y) ≤ (1+4*η)*dist x y := by
  intro x hx y hy
  by_cases hxy : x=y
  · subst y
    simp
  have hd : 0 < dist x y := dist_pos.mpr hxy
  let r := 4*dist x y
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r < R := by dsimp only [r]; linarith [hsmall x hx y hy]
  have hs := happ x hx r hr hrR
  have hh := hs.2.1 x y (by simp only [dist_self]; positivity)
    (by rw [dist_comm]; dsimp only [r]; nlinarith)
  have he : dist (r⁻¹ • (u x-u x)) (r⁻¹ • (u y-u x)) = r⁻¹*dist (u x) (u y) := by
    rw [dist_smul₀,Real.norm_of_nonneg (inv_pos.mpr hr).le,dist_sub_right]
  rw [he] at hh
  have halg : r*(r⁻¹*dist (u x) (u y)-dist x y/r) = dist (u x) (u y)-dist x y := by
    field_simp
  have hscaled : |dist (u x) (u y)-dist x y| ≤ r*η := by
    calc
      _ = |r*(r⁻¹*dist (u x) (u y)-dist x y/r)| := by rw [halg]
      _ = r*|r⁻¹*dist (u x) (u y)-dist x y/r| := by rw [abs_mul,abs_of_pos hr]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hr.le
  have hab := abs_le.mp hscaled
  dsimp only [r] at hab
  constructor <;> nlinarith

theorem all_scale_coordinate_lipschitz {u : X → Euclidean n} {U : Set X} {R η : ℝ}
    (hη : 0 ≤ η) (hsmall : ∀ x ∈ U, ∀ y ∈ U, dist x y < R/4)
    (happ : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation x 0 r (1/2) η (fun z => r⁻¹ • (u z-u x))) :
    LipschitzOnWith ⟨1+4*η,by positivity⟩ u U :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
    (all_scale_coordinate_distance hsmall happ x hx y hy).2

theorem all_scale_coordinate_image_bound [MeasurableSpace X] [BorelSpace X]
    {u : X → Euclidean n} {U : Set X} {R η : ℝ}
    (hη : 0 ≤ η) (hsmall : ∀ x ∈ U, ∀ y ∈ U, dist x y < R/4)
    (happ : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation x 0 r (1/2) η (fun z => r⁻¹ • (u z-u x)))
    (hfin : hausdorff n X U ≠ ⊤) :
    (hausdorff n (Euclidean n)).real (u '' U) ≤ (1+4*η)^n*(hausdorff n X).real U :=
  normalized_hausdorff_real_image_le (all_scale_coordinate_lipschitz hη hsmall happ) hfin

end RegularPointCoordinates

end

end OAI

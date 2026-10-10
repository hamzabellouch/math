import OAI.Geometry.RCD.Metric.HoleImageGeometry

namespace OAI

/-! # A target hole supplies a source ball outside the good set -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- Lift the center of a missing target ball from its boundary contact.
Only the pointed density clause is needed. -/
theorem coordinate_hole_lift {X : Type*} [MetricSpace X] {n : ℕ}
    {u : X → Euclidean n} {z : X} {c : Euclidean n} {r : ℝ} (hr : 0 < r)
    (htouch : dist (u z) c=r)
    (happ : IsPointedApproximation z 0 (64*r) (1/16) (1/128)
      (fun x => (64*r)⁻¹ • (u x-u z))) :
    ∃ x : X, dist x z ≤ 4*r ∧ dist (u x) c ≤ r/2 := by
  let y := (64*r)⁻¹ • (c-u z)
  have hy : dist y 0=1/64 := by
    rw [dist_zero_right]
    dsimp only [y]
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (64*r)⁻¹)]
    have hc : ‖c-u z‖=r := by simpa only [dist_eq_norm,norm_sub_rev] using htouch
    rw [hc]
    field_simp
  obtain ⟨x,hx,hxy⟩ := happ.2.2 y (by rw [hy]; norm_num)
  refine ⟨x,by nlinarith only [hx],?_⟩
  have hh := mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ 64*r)
  have hd : dist ((64*r)⁻¹ • (u x-u z)) y=(64*r)⁻¹*dist (u x) c := by
    dsimp only [y]
    rw [dist_smul₀,Real.norm_of_nonneg (by positivity : 0 ≤ (64*r)⁻¹),dist_sub_right]
  rw [hd] at hh
  have heq : (64*r)*((64*r)⁻¹*dist (u x) c)=dist (u x) c := by field_simp
  rw [heq] at hh
  linarith only [hh]

/-- A Lipschitz source ball around that lift maps strictly inside the hole,
and therefore is disjoint from the original good set. -/
theorem source_ball_avoids_good_set {X : Type*} [MetricSpace X] {n : ℕ}
    {u : X → Euclidean n} {U Ω : Set X} {x : X} {c : Euclidean n} {r C : ℝ}
    (hr : 0 < r) (hC : 0 < C)
    (hsub : ball x (r/(4*C)) ⊆ Ω)
    (hlip : ∀ y ∈ Ω, dist (u y) (u x) ≤ C*dist y x)
    (hclose : dist (u x) c ≤ r/2) (hmiss : Disjoint (ball c r) (u '' U)) :
    (∀ y ∈ ball x (r/(4*C)), u y ∈ ball c r) ∧ Disjoint (ball x (r/(4*C))) U := by
  have himage (y : X) (hy : y ∈ ball x (r/(4*C))) : u y ∈ ball c r := by
    have hh := hlip y (hsub hy)
    have hrad : C*dist y x < r/4 := by
      have hd := mul_lt_mul_of_pos_left (show dist y x < r/(4*C) from hy) hC
      have heq : C*(r/(4*C))=r/4 := by field_simp
      rwa [heq] at hd
    exact mem_ball.mpr (lt_of_le_of_lt (dist_triangle (u y) (u x) c)
      (by linarith only [hh,hrad,hclose,hr]))
  refine ⟨himage,Set.disjoint_left.mpr ?_⟩
  intro y hy hyU
  exact Set.disjoint_left.mp hmiss (himage y hy) (mem_image_of_mem u hyU)

end RegularPointCoordinates

end

end OAI

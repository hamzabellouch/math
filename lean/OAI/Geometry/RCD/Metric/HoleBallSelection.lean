import OAI.Geometry.RCD.Metric.HoleSourceBall

namespace OAI

/-! # Simultaneous source balls for a finite target-hole family -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- The source balls have disjoint images inside disjoint target holes.
Thus their disjointness does not require injectivity of the coordinate map. -/
theorem hole_source_ball_selection {X ι : Type*} [MetricSpace X] {n : ℕ}
    {u : X → Euclidean n} {U Ω : Set X} {C : ℝ} (hC : 0 < C)
    {z : ι → X} {c : ι → Euclidean n} {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htouch : ∀ i, dist (u (z i)) (c i)=r i)
    (happ : ∀ i, IsPointedApproximation (z i) 0 (64*r i) (1/16) (1/128)
      (fun x => (64*r i)⁻¹ • (u x-u (z i))))
    (hroom : ∀ i, ∀ x, dist x (z i) ≤ 4*r i → ball x (r i/(4*C)) ⊆ Ω)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (u x) (u y) ≤ C*dist x y)
    (hmiss : ∀ i, Disjoint (ball (c i) (r i)) (u '' U))
    (hdisj : Pairwise (fun i j => Disjoint (ball (c i) (r i)) (ball (c j) (r j)))) :
    ∃ x : ι → X,
      (∀ i, dist (x i) (z i) ≤ 4*r i) ∧
      (∀ i, ball (x i) (r i/(4*C)) ⊆ Ω \ U) ∧
      Pairwise (fun i j => Disjoint (ball (x i) (r i/(4*C)))
        (ball (x j) (r j/(4*C)))) := by
  choose x hx hclose using fun i => coordinate_hole_lift (hr i) (htouch i) (happ i)
  have hsub (i : ι) : ball (x i) (r i/(4*C)) ⊆ Ω := hroom i (x i) (hx i)
  have hxΩ (i : ι) : x i ∈ Ω := hsub i (mem_ball_self (div_pos (hr i) (by positivity)))
  have hdata (i : ι) := source_ball_avoids_good_set (hr i) hC (hsub i)
    (fun y hy => hlip y hy (x i) (hxΩ i)) (hclose i) (hmiss i)
  refine ⟨x,hx,?_,?_⟩
  · intro i y hy
    exact ⟨hsub i hy,fun hyU => Set.disjoint_left.mp (hdata i).2 hy hyU⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    exact Set.disjoint_left.mp (hdisj hij) ((hdata i).1 y hyi) ((hdata j).1 y hyj)

end RegularPointCoordinates

end

end OAI

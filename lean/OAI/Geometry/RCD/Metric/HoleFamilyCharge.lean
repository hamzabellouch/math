import OAI.Geometry.RCD.Metric.HoleBallSelection
import OAI.Geometry.RCD.Metric.HoleMassCharge

namespace OAI

/-! # Charging target holes to the actual mass omitted by a good set -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.hole_family_charge {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {ι : Type*} [Fintype ι]
    {u : X → Euclidean n} {U Ω : Set X} {p : X} {R C : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hcurv : -1 ≤ K*(2*R)^2)
    (hfin : hausdorff n X (Ω \ U) ≠ ⊤)
    {z : ι → X} {c : ι → Euclidean n} {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htouch : ∀ i, dist (u (z i)) (c i)=r i)
    (happ : ∀ i, IsPointedApproximation (z i) 0 (64*r i) (1/16) (1/128)
      (fun x => (64*r i)⁻¹ • (u x-u (z i))))
    (hroom : ∀ i, ∀ x, dist x (z i) ≤ 4*r i → ball x (r i/(4*C)) ⊆ Ω)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (u x) (u y) ≤ C*dist x y)
    (hmiss : ∀ i, Disjoint (ball (c i) (r i)) (u '' U))
    (hdisj : Pairwise (fun i j => Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (hz : ∀ i, dist (z i) p+4*r i ≤ R) (hrR : ∀ i, r i/(4*C) ≤ R) :
    (∑ i, (r i)^n) ≤
      ((4*C)^n*(Real.cosh 1^(n-1)*2^n)*R^n/(hausdorff n X).real (ball p R))*
        (hausdorff n X).real (Ω \ U) := by
  obtain ⟨x,hxz,hsub,hxdisj⟩ := hole_source_ball_selection hC hr htouch happ hroom hlip hmiss hdisj
  apply hX.hole_mass_charge hn hR hC hcurv hfin (z := x) ?_ hr hrR hsub hxdisj
  intro i
  exact (dist_triangle (x i) (z i) p).trans (by linarith only [hxz i,hz i])

end RegularPointCoordinates

end

end OAI

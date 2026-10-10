import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizingSegments
import OAI.Geometry.WeakMTW.Variations.GeneratingAction

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem chartKinetic_energy (x : M) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target) :
    chartKinetic x q = ‖((stateChart x).symm q).2‖^2/2 := by
  let p := (stateChart (E := Model n) x).symm q
  have hp : p ∈ (stateChart x).source := (stateChart x).map_target hq
  have hh := stateChart_pairing x p.1 ((stateChart_source x p).mp hp) p.2 p.2
  have hcoords : stateChart x p = q := (stateChart x).right_inv hq
  have hh' : metric x (stateChart x p).1 (stateChart x p).2 (stateChart x p).2 = ‖p.2‖^2 := by
    convert (show metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 = ‖p.2‖^2 from
      by simpa only [real_inner_self_eq_norm_sq] using hh) using 1
    rfl
  rw [hcoords] at hh'
  exact congrArg (fun a : ℝ => a/2) hh'

 theorem generatingAction_bound (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (z : Model n) :
    cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm z) ≤
      generatingAction x y ε (q,z) := by
  let p := (stateChart (E := Model n) x).symm q
  let Z := (chartAt (Model n) y).symm z
  let N := ‖p.2‖
  let d := dist (geodesic p (1-ε)) Z
  have hτpos : 0 < 1-ε := sub_pos.mpr hε₁
  have hc : chartCost y ((crossFlowCoordinates x y (1-ε) q).1,z) = cost (geodesic p (1-ε)) Z := by
    change cost ((chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p (1-ε)))) Z = _
    have hτS : geodesic p (1-ε) ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hτ
    rw [(chartAt (Model n) y).left_inv hτS]
  have hd := geodesic_dist_le p 0 (1-ε)
  rw [geodesic_zero,sub_zero,abs_of_pos hτpos] at hd
  have ht : dist p.1 Z ≤ (1-ε)*N + d := by
    exact (dist_triangle p.1 (geodesic p (1-ε)) Z).trans (by dsimp [N,d]; nlinarith)
  have hsq := pow_le_pow_left₀ (dist_nonneg (x := p.1) (y := Z)) ht 2
  have hw := DiscreteVariational.weighted_two_sq ((1-ε)*N) d (1-ε) ε hτpos hε
  have hsum : 1-ε+ε = 1 := by ring
  have hdiv : ((1-ε)*N)^2/(1-ε) = (1-ε)*N^2 := by field_simp
  rw [hsum,div_one,hdiv] at hw
  change dist p.1 Z ^ 2/2 ≤ _
  dsimp only [generatingAction]
  rw [chartKinetic_energy x hq,hc]
  unfold cost
  change dist p.1 Z ^ 2/2 ≤ (1-ε)*(N^2/2)+ε⁻¹*(d^2/2)
  have heq : ε⁻¹*(d^2/2) = (d^2/ε)/2 := by ring
  rw [heq]
  nlinarith

 theorem generatingAction_eq_minimizing (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (h₁ : geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖) :
    generatingAction x y ε (q,(crossFlowCoordinates x y 1 q).1) =
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1) := by
  let p := (stateChart (E := Model n) x).symm q
  have he : (chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1 = geodesic p 1 :=
    (chartAt (Model n) y).left_inv ((stateChart_source y _).mp h₁)
  have hd := minimizing_segment_dist p (L := 1) (a := 1-ε) (b := 1)
    (by simpa only [one_mul] using hm) (sub_nonneg.mpr hε₁.le) (by linarith) le_rfl
  have hc : chartCost y ((crossFlowCoordinates x y (1-ε) q).1,(crossFlowCoordinates x y 1 q).1) =
      cost (geodesic p (1-ε)) (geodesic p 1) := by
    change cost ((chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p (1-ε))))
      ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1) = _
    have hτS : geodesic p (1-ε) ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hτ
    rw [(chartAt (Model n) y).left_inv hτS,he]
  dsimp only [generatingAction]
  rw [chartKinetic_energy x hq,hc,he]
  change (1-ε)*(‖p.2‖^2/2)+ε⁻¹*cost (geodesic p (1-ε)) (geodesic p 1) = cost p.1 (geodesic p 1)
  unfold cost
  rw [hd,hm]
  field_simp
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

import OAI.Geometry.SurfaceImmersion.Geometry.RegularPairAvoidance
import OAI.Geometry.SurfaceImmersion.Geometry.EuclideanSurfaceImageNull

namespace OAI

/-! Arbitrarily small transverse translations remove every coincidence
that uses one of finitely many prescribed points on either coordinate patch. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_small_transverse_translation_avoiding_points {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    (S T : Set Base) (hS : S.Finite) (hT : T.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧
      ∀ x ∈ U, ∀ y ∈ V, f x+a = g y → x ∉ S ∧ y ∉ T ∧
        Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  let N₁ : Set (ProjectionTarget 3) := ⋃ s ∈ S, range (fun y => f s-g y)
  let N₂ : Set (ProjectionTarget 3) := ⋃ t ∈ T, range (fun x => f x-g t)
  have hN₁ : volume N₁ = 0 := (measure_biUnion_null_iff hS.countable).mpr
    (fun s _ => euclidean_surface_image_null _ (contDiff_const.sub hg))
  have hN₂ : volume N₂ = 0 := (measure_biUnion_null_iff hT.countable).mpr
    (fun t _ => euclidean_surface_image_null _ (hf.sub contDiff_const))
  obtain ⟨α,hα,havoid,hreg⟩ := exists_regular_pair_translation_avoiding_null hf hg U V hU hV
    (Metric.ball 0 ε) Metric.isOpen_ball ⟨0,Metric.mem_ball_self hε⟩
    (N₁ ∪ N₂) (measure_union_null hN₁ hN₂)
  refine ⟨-α,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hα
  · intro x hx y hy heq
    have hval : f x-g y = α := by
      apply sub_eq_iff_eq_add.mpr
      calc
        f x = (f x + -α) + α := by abel
        _ = g y + α := by rw [heq]
        _ = α + g y := add_comm _ _
    refine ⟨?_,?_,hreg x hx y hy hval⟩
    · intro hxS
      exact havoid (Or.inl (mem_iUnion₂.mpr ⟨x,hxS,y,hval⟩))
    · intro hyT
      exact havoid (Or.inr (mem_iUnion₂.mpr ⟨y,hyT,x,hval⟩))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

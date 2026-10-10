import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCoordinateBound
import OAI.Geometry.PrescribedPotential.PathCalabiBound
import OAI.Geometry.PrescribedPotential.PathCalabiRicci
import OAI.Geometry.PrescribedPotential.PathEllipticity

namespace OAI

/-! Path Coordinate C1. -/

section

 

noncomputable section
open Set Filter Topology Matrix Metric
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel
local instance pathC1RealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  {A : ComplexAtlas d X}
namespace CoordinateBall
variable (p : CoordinateBall A)

theorem path_coordinate_C1_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A), t ∈ Icc 0 1 →
      ∀ hs : SolvesVolumePath g h t φ b, ∀ x ∈ p.source,
        ‖(g.deform φ hs.choose).matrix p.index (A.chart p.index x)‖ ≤ C ∧
        ‖fderiv ℝ (fun z i j => (g.deform φ hs.choose).matrix p.index z i j)
          (A.chart p.index x)‖ ≤ C := by
  obtain ⟨S,hS,hcal⟩ := p.path_calabi_bound g h
  obtain ⟨R,H,hR,hH,hell⟩ := volumePath_relative_ellipticity g h
  let L : Set (V d) := coordinateEquiv d '' closedBall p.center p.radius
  have hL : IsCompact L := (isCompact_closedBall _ _).image (coordinateEquiv d).continuous
  have hLc (z : V d) : z ∈ L ↔ (coordinateEquiv d).symm z ∈ closedBall p.center p.radius := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
    · intro hz
      exact ⟨_,hz,(coordinateEquiv d).apply_symm_apply z⟩
  have hdom : L ⊆ (A.chart p.index).target := by
    intro z hz
    have hh := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) ((hLc z).mp hz))
    simpa only [ComplexAtlas.euclideanChart_target,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hh
  obtain ⟨C,hC,hbound⟩ := calabi_coordinate_C1_uniform hL (g.matrix p.index)
    ((g.smooth p.index).continuousOn.mono hdom) (fun z hz => g.positive _ _ (hdom hz)) hR.le hH.le hS
  refine ⟨C,hC,?_⟩
  intro t b φ ht hs x hx
  have hz : A.chart p.index x ∈ L := (hLc _).mpr (ball_subset_closedBall hx.2)
  obtain ⟨hl,hu⟩ := hell t b φ ht hs p.index _ (hdom hz)
  exact hbound _ hz ((g.deform φ hs.choose).localField p.index) _ (hdom hz) hl hu
    (hcal t b φ ht hs x hx)
end CoordinateBall

 
theorem volumePath_coordinate_C1_finite_cover (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ (S : Finset (CoordinateBall A)) (C : ℝ), 0 ≤ C ∧
      (∀ x, ∃ p ∈ S, x ∈ p.source) ∧
      ∀ p ∈ S, ∀ (t b : ℝ) (φ : SmoothRealFunction A), t ∈ Icc 0 1 →
        ∀ hs : SolvesVolumePath g h t φ b, ∀ x ∈ p.source,
          ‖(g.deform φ hs.choose).matrix p.index (A.chart p.index x)‖ ≤ C ∧
          ‖fderiv ℝ (fun z i j => (g.deform φ hs.choose).matrix p.index z i j)
            (A.chart p.index x)‖ ≤ C := by
  classical
  obtain ⟨S,hS⟩ := CoordinateBall.finite_cover (A := A)
  choose C hC hb using fun p : CoordinateBall A => p.path_coordinate_C1_bound g h
  refine ⟨S,∑ p ∈ S, C p,Finset.sum_nonneg (fun p _ => hC p),hS,?_⟩
  intro p hp t b φ ht hs x hx
  have hle := Finset.single_le_sum (fun q _ => hC q) hp
  exact ⟨(hb p t b φ ht hs x hx).1.trans hle,(hb p t b φ ht hs x hx).2.trans hle⟩
end Anticanonical.SourceSmooth

end
end

end OAI

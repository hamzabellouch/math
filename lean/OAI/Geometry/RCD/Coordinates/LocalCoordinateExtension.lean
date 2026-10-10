import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Measurable extensions preserving the local metric approximation -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- Only values on the closed testing ball enter a pointed approximation. -/
theorem IsPointedApproximation.congr_on_ball {Y : Type*} [MetricSpace Y]
    {p : X} {q : Y} {r R ε : ℝ} {f g : X → Y}
    (hRr : 0 ≤ R * r) (hf : IsPointedApproximation p q r R ε f)
    (hfg : EqOn f g (closedBall p (R * r))) :
    IsPointedApproximation p q r R ε g := by
  have hp : f p = g p := hfg (by simpa only [mem_closedBall, dist_self] using hRr)
  refine ⟨by simpa only [hp] using hf.1, ?_, ?_⟩
  · intro x y hx hy
    rw [← hfg hx, ← hfg hy]
    exact hf.2.1 x y hx hy
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hf.2.2 y hy
    exact ⟨x, hx, by rwa [← hfg hx]⟩

/-- A continuous local coordinate map has a measurable extension which
agrees pointwise throughout its open domain. -/
theorem exists_measurable_local_extension [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasurableSet s) {v : X → Euclidean n}
    (hv : ContinuousOn v s) :
    ∃ v' : X → Euclidean n, Measurable v' ∧ EqOn v v' s := by
  classical
  refine ⟨s.piecewise v (fun _ => 0),
    hv.measurable_piecewise continuous_const.continuousOn hs, ?_⟩
  intro x hx
  simp only [piecewise_eq_of_mem s v (fun _ => 0) hx]

end RegularPointCoordinates

end

end OAI

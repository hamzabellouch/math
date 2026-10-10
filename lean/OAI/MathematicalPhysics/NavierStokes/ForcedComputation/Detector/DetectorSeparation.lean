import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatEvolution

namespace OAI

/-! Full-orbit separation excludes a false observation both during a
burst and during its subsequent heat evolution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem torusNorm_zero : torusNorm (0 : Plane) = 0 := by
  have he : centeredRepresentative (0 : Plane) = 0 := by
    ext j
    norm_num [centeredRepresentative]
  rw [torusNorm, he, map_zero, norm_zero]

theorem detectorReference_separated {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hv : PlanarVariations V Ψ) (hV : ∀ s, ContDiff ℝ ∞ (V s))
    (hp : ∀ s, PlanePeriodic (V s)) (C L n : ℕ)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    {E : Set Plane}
    (hfar : ∀ s, 0 ≤ s → ∀ x ∈ E,
      1 / 16 ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x))
    (t : ℝ) {x y : Plane} (hx : x ∈ E)
    (hy : detectorReference Ψ C L n t y ≠ 0) :
    (1 / 32 : ℝ) ^ 2 ≤ torusDistanceSq (x - y) := by
  have hn := detectorReference_support_near hΨ hv hV hp C L n h₁ hy
  have hs := detectorPhase_range C L n t
  have hf := hfar (detectorPhase C L n t) hs.1 x hx
  have hd : (1 / 32 : ℝ) ≤ torusNorm (x - y) :=
    torus_separation hn (by norm_num at hf ⊢; exact hf) le_rfl
  rw [← torusNorm_sq]
  nlinarith [torusNorm_nonneg (x - y)]

theorem detectorReference_zero_on_target {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hv : PlanarVariations V Ψ) (hV : ∀ s, ContDiff ℝ ∞ (V s))
    (hp : ∀ s, PlanePeriodic (V s)) (C L n : ℕ)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    {E : Set Plane}
    (hfar : ∀ s, 0 ≤ s → ∀ x ∈ E,
      1 / 16 ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x))
    (t : ℝ) {x : Plane} (hx : x ∈ E) : detectorReference Ψ C L n t x = 0 := by
  by_contra hn
  have h := detectorReference_separated hΨ hv hV hp C L n h₁ hfar t hx hn
  rw [sub_self, ← torusNorm_sq, torusNorm_zero] at h
  norm_num at h

theorem detectorReference_heat_bound (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (hv : PlanarVariations V Ψ)
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    {E : Set Plane}
    (hfar : ∀ s, 0 ≤ s → ∀ x ∈ E,
      1 / 16 ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x))
    (t : ℝ) {τ : ℝ} (hτ : 0 < τ) {x : Plane} (hx : x ∈ E) :
    torusHeatEvolution (detectorReference Ψ C L n t) τ x ≤
      1000000000 * (4 * (width L n : ℝ) ^ 2) := by
  have hVs : ∀ s, ContDiff ℝ ∞ (V s) :=
    fun s => hV.comp (contDiff_const.prodMk contDiff_id)
  have hbound := torusHeatEvolution_mass_bound hK
    ((detectorReference_smooth hback C L n).comp
      (contDiff_const.prodMk contDiff_id)).continuous
    (fun y => (detectorReference_range Ψ C L n t y).1) hτ x
    (fun y _ hy => ((torusHeatKernel_detector_bounds hK hτ (x - y)).1
      (Or.inr (detectorReference_separated hΨ hv hVs hp C L n h₁ hfar t hx hy))).le)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (detectorReference_mass hΨ hV hp hdiv hback C L n t).2 (by norm_num))

end ForcedComputation.VelocityDetector

end

end OAI

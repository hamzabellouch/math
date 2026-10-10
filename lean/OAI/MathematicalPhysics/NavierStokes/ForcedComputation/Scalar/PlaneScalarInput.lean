import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! Smooth scalar advection-diffusion on the whole plane.

Ladyzhenskaya, Solonnikov and Ural'tseva, Linear and Quasi-linear Equations
of Parabolic Type, AMS Translations of Mathematical Monographs 23 (1968),
Chapter IV, Theorem 5.1, p.320; Cauchy problem (5.1)--(5.2), p.318 and
bounded Hölder classes, p.319. We specialize to positive constant diffusion,
smooth drift and source with common compact support on each finite slab,
and zero initial data. Higher Hölder orders give smoothness up to the initial
time from the right. The choice of Hölder order 3/2 also bounds spatial
derivatives through order three on each finite slab.
 -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def CompactPlaneCoefficients (a : ℝ → Plane → Plane) (h : ℝ → Plane → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set Plane, IsCompact K ∧
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, x ∉ K → a t x = 0 ∧ h t x = 0

structure PlaneScalarSolution (T ν : ℝ) (a : ℝ → Plane → Plane)
    (h w : ℝ → Plane → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ univ)
  initial : w 0 = fun _ => 0
  equation : ∀ t ∈ Icc 0 T, ∀ x,
    HasDerivWithinAt (fun s => w s x)
      (scalarGenerator ν (a t) (w t) x + h t x) (Icc 0 T) t
  bounded : ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
    |w t x| ≤ B ∧ ‖fderiv ℝ (w t) x‖ ≤ B

/-- Only the orders needed for local tail and H² estimates are retained.
The bound may depend on the finite time interval and the coefficients. -/
def PlaneSpatialBounds (T : ℝ) (w : ℝ → Plane → ℝ) : Prop :=
  ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ k : ℕ, k ≤ 3 → ∀ x,
    ‖iteratedFDeriv ℝ k (w t) x‖ ≤ B

def PlaneScalarExistence : Prop :=
  ∀ (T ν : ℝ), 0 < T → 0 < ν →
    ∀ (a : ℝ → Plane → Plane) (h : ℝ → Plane → ℝ),
    ContDiff ℝ ∞ (Function.uncurry a) →
    ContDiff ℝ ∞ (Function.uncurry h) → CompactPlaneCoefficients a h →
    ∃ w, PlaneScalarSolution T ν a h w ∧ PlaneSpatialBounds T w

theorem PlaneScalarSolution.slice_smooth {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (w t) := by
  have hi : ContDiff ℝ ∞ (fun x : Plane => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hh := hw.smooth.comp hi.contDiffOn
    (show MapsTo (fun x : Plane => (t, x)) univ (Icc 0 T ×ˢ univ) from
      fun x _ => ⟨ht, mem_univ x⟩)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, contDiffOn_univ] using hh

end ForcedComputation.VelocityDetector

end

end OAI

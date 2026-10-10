import OAI.Geometry.RCD.Coordinates.PatchCoverData
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import OAI.Geometry.RCD.Coordinates.FrozenJetTransport

namespace OAI

/-!
# Euclidean Gevrey cutoffs of order two

L. Hörmander, *Between distributions and hyperfunctions*, Astérisque 131
(1985), pp. 89–106, §2, equations (2.2) and (2.6), p. 90, describes
nonquasianalytic Gevrey classes containing compactly supported functions.
Squaring a nonzero bump and convolving its normalized dilation with a ball
indicator gives a fixed core and support. Equivalence of coordinate
and finite-dimensional multilinear derivative bounds changes only the
exponential constant.

https://numdam.org/item/AST_1985__131__89_0.pdf
-/

open Set Metric
open scoped ContDiff

noncomputable section
namespace RegularPointCoordinates

/-- A single fixed radial-scale cutoff with all-order Gevrey-two bounds. -/
structure EuclideanGevreyCutoff (n : ℕ) where
  value : Euclidean n → ℝ
  constant : ℝ
  constant_ge_one : 1 ≤ constant
  smooth : ContDiff ℝ ∞ value
  nonneg : ∀ z, 0 ≤ value z
  le_one : ∀ z, value z ≤ 1
  core : ∀ z, ‖z‖ ≤ 2 → value z = 1
  support : tsupport value ⊆ closedBall 0 3
  jet : ∀ (m : ℕ) (z : Euclidean n),
    ‖iteratedFDeriv ℝ m value z‖ ≤ constant ^ (m + 1) * (m.factorial : ℝ) ^ 2

/-- The precise compact Gevrey specialization needed by the chart proof. -/
def EuclideanGevreyCutoffInput (n : ℕ) : Prop := Nonempty (EuclideanGevreyCutoff n)

/-- A fixed affine change preserves the Gevrey order. The base records the
actual operator norm, while the derivative order remains unrestricted. -/
theorem EuclideanGevreyCutoff.affine_jet_le {n : ℕ} (psi : EuclideanGevreyCutoff n)
    (L : Euclidean n →L[ℝ] Euclidean n) (a z : Euclidean n) (m : ℕ)
    {M : ℝ} (hM : 1 ≤ M) (hL : ‖L‖ ≤ M) :
    ‖iteratedFDeriv ℝ m (fun w => psi.value (a + L w)) z‖ ≤
      (psi.constant * M) ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  have hc : 0 ≤ psi.constant := zero_le_one.trans psi.constant_ge_one
  have hbound := norm_iteratedFDeriv_comp_affine_le L psi.value a z m
    (psi.smooth.of_le (by simp)).contDiffAt
  have hp : ‖L‖ ^ m ≤ M ^ (m + 1) :=
    (pow_le_pow_left₀ (norm_nonneg L) hL m).trans
      (pow_le_pow_right₀ hM (by omega))
  calc
    _ ≤ ‖iteratedFDeriv ℝ m psi.value (a + L z)‖ * ‖L‖ ^ m := hbound
    _ ≤ (psi.constant ^ (m + 1) * (m.factorial : ℝ) ^ 2) * M ^ (m + 1) :=
      mul_le_mul (psi.jet m _) hp (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end RegularPointCoordinates

end

end OAI

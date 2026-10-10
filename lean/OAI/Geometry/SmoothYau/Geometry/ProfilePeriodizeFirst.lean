import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ProfilePeriodizeEventuallyZero

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profileLattice_separated {k l : ProfileLattice} (hkl : k ≠ l) :
    1 ≤ ‖profileLatticePoint k - profileLatticePoint l‖ := by
  have hne : k.1 ≠ l.1 ∨ k.2 ≠ l.2 := by
    by_contra h
    push Not at h
    exact hkl (Prod.ext h.1 h.2)
  rw [Prod.norm_def]
  rcases hne with h | h
  · have hh : (1:ℝ) ≤ |(k.1:ℝ)-(l.1:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    exact hh.trans (le_max_left _ _)
  · have hh : (1:ℝ) ≤ |(k.2:ℝ)-(l.2:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    exact hh.trans (le_max_right _ _)

theorem profilePeriodize_single {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (k : ProfileLattice) {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ ≤ R) :
    profilePeriodize f x = f (x-profileLatticePoint k) := by
  unfold profilePeriodize
  apply finsum_eq_single
  intro l hl
  apply hf
  have hsep := profileLattice_separated hl
  have htri : ‖profileLatticePoint l-profileLatticePoint k‖ ≤
      ‖x-profileLatticePoint l‖+‖x-profileLatticePoint k‖ := by
    calc
      _ = ‖(profileLatticePoint l-x)+(x-profileLatticePoint k)‖ := by congr 1; abel
      _ ≤ ‖profileLatticePoint l-x‖+‖x-profileLatticePoint k‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (profileLatticePoint l) x]
  linarith

theorem profilePeriodize_eventually_single {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (k : ProfileLattice) {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ < R) :
    profilePeriodize f =ᶠ[𝓝 x] (fun z => f (z-profileLatticePoint k)) := by
  have ho : IsOpen {z : ProfilePlane | ‖z-profileLatticePoint k‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [ho.mem_nhds hx] with z hz
  exact profilePeriodize_single hR hf k (le_of_lt hz)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profilePeriodize_first {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (hs : Differentiable ℝ f) (k : ProfileLattice) {x : ProfilePlane}
    (hx : ‖x-profileLatticePoint k‖ < R) (v : ProfilePlane) :
    fderiv ℝ (profilePeriodize f) x v = fderiv ℝ f (x-profileLatticePoint k) v := by
  rw [(profilePeriodize_eventually_single hR hf k hx).fderiv_eq]
  have hh := (hs (x-profileLatticePoint k)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (profileLatticePoint k))
  erw [hh.fderiv]
  simp

theorem profilePeriodize_second {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (hs : ContDiff ℝ ∞ f) (k : ProfileLattice) {x : ProfilePlane}
    (hx : ‖x-profileLatticePoint k‖ < R) (v w : ProfilePlane) :
    fderiv ℝ (fun z => fderiv ℝ (profilePeriodize f) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ f z w) (x-profileLatticePoint k) v := by
  have ho : IsOpen {z : ProfilePlane | ‖z-profileLatticePoint k‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have he : (fun z => fderiv ℝ (profilePeriodize f) z w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ f (z-profileLatticePoint k) w) := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact profilePeriodize_first hR hf (hs.differentiable (by simp)) k hz w
  rw [he.fderiv_eq]
  have hD := (hs.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hh := ((hD (x-profileLatticePoint k)).clm_apply
    (differentiableAt_const w)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (profileLatticePoint k))
  erw [hh.fderiv]
  simp



end YauCounterexamples
end

end OAI

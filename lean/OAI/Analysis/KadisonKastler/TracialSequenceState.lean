import OAI.Analysis.KadisonKastler.VaryingSequence
import OAI.Analysis.KadisonKastler.TracialProducts
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # The canonical trace on a bounded product

The trace is the scalar ultralimit of the coordinate traces. The varying
family covers both the constant-factor and finite-matrix products used here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

theorem exists_tracialSequenceValue (x : VaryingBoundedSequence B) :
    ∃ z : ℂ, ‖z‖ ≤ ‖x‖ ∧ Tendsto (fun j => (τ j).toLinearMap (x j))
      (ω : Filter ℕ) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖x‖).ultrafilter_le_nhds
    (ω.map (fun j => (τ j).toLinearMap (x j))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ j in (ω : Filter ℕ), (τ j).toLinearMap (x j) ∈ Metric.closedBall (0 : ℂ) ‖x‖
      exact Eventually.of_forall (fun j => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          ((τ j).norm_apply_le_norm (x j)).trans (varyingSequence_norm_apply_le x j)))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

def tracialSequenceValue (x : VaryingBoundedSequence B) : ℂ :=
  Classical.choose (exists_tracialSequenceValue τ ω x)

theorem norm_tracialSequenceValue (x : VaryingBoundedSequence B) :
    ‖tracialSequenceValue τ ω x‖ ≤ ‖x‖ :=
  (Classical.choose_spec (exists_tracialSequenceValue τ ω x)).1

theorem tendsto_tracialSequenceValue (x : VaryingBoundedSequence B) :
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 (tracialSequenceValue τ ω x)) :=
  (Classical.choose_spec (exists_tracialSequenceValue τ ω x)).2

def tracialSequenceLinear : VaryingBoundedSequence B →ₗ[ℂ] ℂ where
  toFun := tracialSequenceValue τ ω
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (x + y))
    simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
      (tendsto_tracialSequenceValue τ ω x).add (tendsto_tracialSequenceValue τ ω y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (c • x))
    simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply] using
      (tendsto_tracialSequenceValue τ ω x).const_smul c

def tracialSequenceContinuous : VaryingBoundedSequence B →L[ℂ] ℂ :=
  (tracialSequenceLinear τ ω).mkContinuous 1 (fun x => by
    change ‖tracialSequenceValue τ ω x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_tracialSequenceValue τ ω x)

@[simp] theorem tracialSequenceContinuous_apply (x : VaryingBoundedSequence B) :
    tracialSequenceContinuous τ ω x = tracialSequenceValue τ ω x := rfl

variable [∀ j, Nontrivial (B j)]

@[simp] theorem tracialSequenceValue_one : tracialSequenceValue τ ω 1 = 1 := by
  apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω 1)
  simpa only [lp.infty_coeFn_one, Pi.one_apply, FaithfulTracialState.map_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_tracial (x y : VaryingBoundedSequence B) :
    tracialSequenceValue τ ω (x * y) = tracialSequenceValue τ ω (y * x) := by
  apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (x * y))
  simpa only [lp.infty_coeFn_mul, Pi.mul_apply, FaithfulTracialState.tracial] using
    tendsto_tracialSequenceValue τ ω (y * x)

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_positive (x : VaryingBoundedSequence B) :
    0 ≤ (tracialSequenceValue τ ω (star x * x)).re := by
  apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_tracialSequenceValue τ ω (star x * x)))
  exact Eventually.of_forall (fun j => (τ j).positive (x j))

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_positive_im (x : VaryingBoundedSequence B) :
    (tracialSequenceValue τ ω (star x * x)).im = 0 := by
  apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp
    (tendsto_tracialSequenceValue τ ω (star x * x)))
  simpa only [Function.comp_def, lp.infty_coeFn_mul, lp.coeFn_star, Pi.mul_apply,
    Pi.star_apply, FaithfulTracialState.positive_im] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0))

end

end KadisonKastler

end OAI

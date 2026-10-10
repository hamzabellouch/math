import OAI.Analysis.LipschitzHilbert.Phase.DiagonalPhaseSelection
import OAI.Analysis.LipschitzHilbert.Estimates.NeighborhoodEnergy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! Remove the vertical carrier before applying the interval Sobolev
estimate. The derivative norm is exactly the covariant derivative norm,
independently of the carrier frequencies and Hilbert dimension. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
open PhaseCombinatorics

theorem character_hasDerivAt (frequency y : ℝ) :
    HasDerivAt (character frequency) ((frequency:ℂ)*Complex.I*character frequency y) y := by
  have h := (((hasDerivAt_id y).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    change (frequency:ℂ)*Complex.I*character frequency y =
      character frequency y*((frequency:ℂ)*Complex.I)
    ring

def demodulatedSignal {κ : Type*} (frequency : κ → ℝ) (f : κ → ℝ → ℂ)
    (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => f k y * character (-frequency k) y)

def covariantSignal {κ : Type*} (frequency : κ → ℝ) (f : κ → ℝ → ℂ)
    (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y)

theorem demodulatedSignal_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ) :
    ‖demodulatedSignal frequency f y‖ = ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ :=
  norm_diagonalModulation (fun k => -frequency k) (WithLp.toLp 2 (fun k => f k y)) y

theorem demodulatedSignal_hasDerivAt {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    HasDerivAt (demodulatedSignal frequency f)
      (diagonalModulation (fun k => -frequency k) (covariantSignal frequency f y) y) y := by
  have hc : HasDerivAt (fun t k => f k t * character (-frequency k) t)
      (fun k => (deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y) *
        character (-frequency k) y) y := by
    apply hasDerivAt_pi.mpr
    intro k
    have h := (hf k).hasDerivAt.mul (character_hasDerivAt (-frequency k) y)
    convert h using 1
    push_cast
    ring
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y hc

theorem demodulatedSignal_deriv_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    ‖deriv (demodulatedSignal frequency f) y‖ = ‖covariantSignal frequency f y‖ := by
  rw [(demodulatedSignal_hasDerivAt frequency f y hf).deriv, norm_diagonalModulation]

theorem demodulated_deriv_memLp {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (μ : Measure ℝ)
    (hf : ∀ᵐ y ∂μ, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 μ) :
    MemLp (deriv (demodulatedSignal frequency f)) 2 μ := by
  apply hD.congr_norm (aestronglyMeasurable_deriv _ μ)
  filter_upwards [hf] with y hy
  exact (demodulatedSignal_deriv_norm frequency f y hy).symm

theorem covariant_interval_energy {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hf : ∀ y ∈ Set.Icc a b, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 (volume.restrict (Set.Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Set.Icc a b)) (hDC : ContinuousOn D (Set.Icc a b))
    (hbV : ∀ y ∈ Set.Icc a b, ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ ≤ V y)
    (hbD : ∀ y ∈ Set.Icc a b, ‖covariantSignal frequency f y‖ ≤ D y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖(WithLp.toLp 2 (fun k => f k x) : EuclideanSpace ℂ κ)‖^2 ≤
      verticalSquareEnergy (volume.restrict (Set.Icc a b)) V (fun t => (b-a)*D t) := by
  have hd := demodulated_deriv_memLp frequency f (volume.restrict (Set.Icc a b))
    ((ae_restrict_mem measurableSet_Icc).mono fun y hy => hf y hy) hD
  have h := interval_energy_domination (demodulatedSignal frequency f) hab
    (fun y hy => (demodulatedSignal_hasDerivAt frequency f y (hf y hy)).differentiableAt)
    hd V D hV hDC
    (fun y hy => by rw [demodulatedSignal_norm]; exact hbV y hy)
    (fun y hy => by rw [demodulatedSignal_deriv_norm frequency f y (hf y hy)]; exact hbD y hy) hx
  simpa only [demodulatedSignal_norm] using h

end LipschitzHilbert

end

end OAI

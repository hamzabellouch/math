import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument
import OAI.Analysis.CircleDomains.Topology.JordanContours
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace OAI

/-! The precise classical Green input used below.

M. Spivak, Calculus on Manifolds (1965), Theorem 5-5, p.124,
Stokes' theorem on a compact oriented manifold with boundary. The
specialization is a bounded smooth Jordan region with finitely many
pairwise disjoint round holes and a smooth real one-form. Circle
boundaries have positive disk orientation, so their integrals are
subtracted. The compact region lies inside the open set of smoothness.
https://www.cimat.mx/~gil/docencia/2013/topologia_variedades/spivak-calculus-on-manifolds.pdf -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

/-- A positively oriented regular parametrization of the actual Jordan
boundary. Positivity is specified by the real argument lift around
interior points, independently of any integration formula. -/
structure PositiveJordanParametrization (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) γ
  periodic : Function.Periodic γ 1
  injective : InjOn γ (Ico 0 1)
  regular : ∀ t, deriv γ t ≠ 0
  boundary : γ '' Icc 0 1 = frontier (jordanInterior H)
  positive : ∀ z ∈ jordanInterior H, ∃ u : C(unitInterval, ℝ),
    (∀ t, (u t : UnitAddCircle) = normalizedArgument (γ t - z)) ∧ u 1 = u 0 + 1

/-- Real line integral of `P dx + Q dy`, with parameter interval `[0,1]`. -/
def planarFormIntegral (P Q : ℂ → ℝ) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im

def unitCircleParam (c : ℂ) (r : ℝ) (t : ℝ) : ℂ := circleMap c r (2 * Real.pi * t)

/-- Published input: the finite-round-hole planar specialization of
Spivak's Theorem5-5. All geometric boundaries and integrals are explicit. -/
def FiniteCircleGreenFormula : Prop :=
  ∀ (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ), PositiveJordanParametrization H γ →
  ∀ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
    (∀ i, 0 < r i) →
    Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)) →
    (∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H) →
  ∀ O : Set ℂ, IsOpen O →
    (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O →
  ∀ P Q : ℂ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) P O → ContDiffOn ℝ (⊤ : ℕ∞) Q O →
    planarFormIntegral P Q γ - ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) =
      ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I

/-- The weighted Green identity for an actual closed real one-form.
Closedness removes the second-derivative term; no Stokes estimate is assumed. -/
theorem finiteCircleGreen_weighted_closed_form
    (hgreen : FiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)))
    (hin : ∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O)
    (φ P Q : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O)
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O) (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O)
    (hclosed : ∀ z ∈ O, (fderiv ℝ Q z) 1 = (fderiv ℝ P z) Complex.I) :
    planarFormIntegral (φ * P) (φ * Q) γ -
      ∑ i, planarFormIntegral (φ * P) (φ * Q) (unitCircleParam (c i) (r i)) =
      ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
        (fderiv ℝ φ z) 1 * Q z - (fderiv ℝ φ z) Complex.I * P z := by
  rw [hgreen H γ hγ n c r hr hd hin O hO hsub (φ * P) (φ * Q) (hφ.mul hP) (hφ.mul hQ)]
  apply setIntegral_congr_fun
  · exact (jordanInterior_isOpen H).measurableSet.diff (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  · intro z hz
    have hzO : z ∈ O := hsub ⟨subset_closure hz.1, fun hm => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact hz.2 (mem_iUnion.mpr ⟨i, Metric.ball_subset_closedBall hi⟩)⟩
    have hφd := (hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hPd := (hP.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hQd := (hQ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    change (fderiv ℝ (φ * Q) z) 1 - (fderiv ℝ (φ * P) z) Complex.I =
      (fderiv ℝ φ z) 1 * Q z - (fderiv ℝ φ z) Complex.I * P z
    rw [fderiv_mul hφd hQd, fderiv_mul hφd hPd]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hclosed z hzO]
    ring

end CircleDomainRigidity

end

end OAI

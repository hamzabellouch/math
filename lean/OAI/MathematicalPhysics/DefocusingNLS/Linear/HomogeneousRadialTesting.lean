import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialSchwartz
import Mathlib.Data.Fin.Rev

namespace OAI

/-! # Integration by parts along each radial line

This is the dense-domain testing identity for the completed contraction.
Tests supported in the positive half-line can later be multiplied by r^11
before this identity is applied.
-/

open MeasureTheory Set LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem scalar_schwartz_iterated_ibp (N : ℕ) (v : Fin N → ℝ)
    (ψ f : 𝓢(ℝ, ℂ)) :
    (∫ r : ℝ, inner ℝ (ψ r) ((∂^{v} f) r)) =
      (-1 : ℝ) ^ N * ∫ r : ℝ, inner ℝ ((∂^{fun i => v (Fin.rev i)} ψ) r) (f r) := by
  induction N generalizing ψ f with
  | zero => simp
  | succ N ih =>
      rw [iteratedLineDerivOp_succ_left]
      have hibp := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
        (μ := (volume : Measure ℝ)) ψ (∂^{Fin.tail v} f) (innerSL ℝ) (v 0)
      change (∫ r : ℝ, inner ℝ (ψ r) ((∂_{v 0} (∂^{Fin.tail v} f)) r)) =
        -(∫ r : ℝ, inner ℝ ((∂_{v 0} ψ) r) ((∂^{Fin.tail v} f) r)) at hibp
      rw [hibp, ih (Fin.tail v) (∂_{v 0} ψ) f]
      have ht : (∂^{fun i => v (Fin.rev i)} ψ) =
          ∂^{fun i => Fin.tail v (Fin.rev i)} (∂_{v 0} ψ) := by
        rw [iteratedLineDerivOp_succ_right]
        simp only [Fin.rev_last]
        congr 1
        funext i
        simp only [Fin.init_def, Fin.tail_def, Fin.rev_castSucc]
      rw [ht, pow_succ]
      ring

/-- Restrict a Schwartz function to a radial line through a unit vector. -/
noncomputable def schwartzRadialRestriction (ω : PhysicalUnitSphere) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  let L := LinearIsometry.toSpanSingleton ℝ E
    (show ‖ω.1‖ = 1 by simpa only [Metric.mem_sphere, dist_zero_right] using ω.2)
  exact SchwartzMap.compCLMOfAntilipschitz ℂ
    L.toContinuousLinearMap.hasTemperateGrowth L.isometry.antilipschitzWith

@[simp] theorem schwartzRadialRestriction_apply (ω : PhysicalUnitSphere)
    (f : 𝓢(E, ℂ)) (r : ℝ) : schwartzRadialRestriction ω f r = f (r • ω.1) := rfl

/-- The contracted top Cartesian derivative has the expected scalar
integration-by-parts formula on every fixed radial line. -/
theorem schwartz_radial_integral_by_parts (N : ℕ) (ψ : 𝓢(ℝ, ℂ))
    (f : 𝓢(E, ℂ)) (ω : PhysicalUnitSphere) :
    (∫ r : ℝ, inner ℝ (ψ r)
      (∑ j : Fin N → Fin 12, (radialTensorCoefficient N j ω : ℂ) *
        homogeneousOrderedDerivative N j f (r • ω.1))) =
      (-1 : ℝ) ^ N * ∫ r : ℝ,
        inner ℝ ((∂^{fun _ : Fin N => (1 : ℝ)} ψ) r) (f (r • ω.1)) := by
  have h := scalar_schwartz_iterated_ibp N (fun _ : Fin N => (1 : ℝ))
    ψ (schwartzRadialRestriction ω f)
  have hj (r : ℝ) : (∂^{fun _ : Fin N => (1 : ℝ)}
      (schwartzRadialRestriction ω f)) r =
      ∑ j : Fin N → Fin 12, (radialTensorCoefficient N j ω : ℂ) *
        homogeneousOrderedDerivative N j f (r • ω.1) := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    change iteratedDeriv N (fun t : ℝ => f (t • ω.1)) r = _
    exact schwartz_radial_iteratedDeriv N f ω r
  simpa only [hj, schwartzRadialRestriction_apply] using h

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalParameterZero
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousCoordinateStableOrbit

namespace OAI

/-! # Physical parameter selection on the continuous flat stable graph -/

open Set Metric
namespace DefocusingNLS
local notation "Params" => ProfileSymmetryParameters
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem flatStableGraph_intersection
    (C : Params ≃L[ℝ] V) (r ρ L₀ ε ν η W : ℝ)
    (hr : 0 ≤ r) (hν : 0 ≤ ν) (hW : W ≤ ρ / 4)
    (π : Radius → FourierL2 →L[ℝ] V) (ζ : Radius → V →L[ℝ] FourierL2)
    (hπc : Continuous (fun q : Radius × FourierL2 => π q.1 q.2))
    (hζc : ContinuousOn ζ {L : Radius | L₀ ≤ L.1})
    (hinv : ∀ L : Radius, L₀ ≤ L.1 → ∀ v, π L (ζ L v) = v)
    (G : CutoffStableParameter ρ L₀ π → FourierL2) (hGc : Continuous G)
    (hGstable : ∀ q, stableFrameProjection (ζ q.1.1) (π q.1.1) (G q) = q.1.2)
    (hGflat : ∀ q, ‖π q.1.1 (G q)‖ ≤ ν * (‖q.1.2‖ + 2 * η) + 2 * η)
    (L : closedBall (0 : Params) r → Radius) (hLc : Continuous L)
    (hL : ∀ p, L₀ ≤ (L p).1)
    (f : closedBall (0 : Params) r → FourierL2) (hfc : Continuous f)
    (hwbound : ∀ p, ‖stableFrameProjection (ζ (L p)) (π (L p)) (f p)‖ ≤ W)
    (herror : ∀ p, ‖π (L p) (f p) - C p.1‖ ≤ ε)
    (hsmall : ‖C.symm.toContinuousLinearMap‖ * (ε + ν * (W + 2 * η) + 2 * η) ≤ r) :
    ∃ p, ∃ q : CutoffStableParameter ρ L₀ π, q.1.1 = L p ∧ G q = f p := by
  let w := fun p => stableFrameProjection (ζ (L p)) (π (L p)) (f p)
  have hzc : Continuous (fun p => ζ (L p)) := hζc.comp_continuous hLc hL
  have hpc : Continuous (fun p => π (L p) (f p)) := hπc.comp (hLc.prodMk hfc)
  have hwc : Continuous w := hfc.sub (hzc.clm_apply hpc)
  let Q := fun p : closedBall (0 : Params) r =>
    (⟨(L p, w p), hL p, (hwbound p).trans hW,
      stableFrameProjection_coordinate _ _ (hinv (L p) (hL p)) (f p)⟩ :
        CutoffStableParameter ρ L₀ π)
  have hQc : Continuous Q := (hLc.prodMk hwc).subtype_mk _
  obtain ⟨p, hp⟩ := physical_parameter_zero_of_coordinate_bound C r ε
    (ν * (W + 2 * η) + 2 * η) hr f (fun p => G (Q p))
    (fun p => π (L p)) (fun p => ζ (L p)) hfc (hGc.comp hQc)
    (hπc.comp ((hLc.comp continuous_fst).prodMk continuous_snd)) herror
    (fun p => (hGflat (Q p)).trans (by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (hwbound p) le_rfl) hν) le_rfl))
    (fun p => hGstable (Q p)) (by simpa only [add_assoc] using hsmall)
  exact ⟨p, Q p, rfl, hp.symm⟩

end DefocusingNLS

end OAI

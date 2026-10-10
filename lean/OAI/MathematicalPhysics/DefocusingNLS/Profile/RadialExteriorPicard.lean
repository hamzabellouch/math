import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorSource
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! The nonlinear backward tail equation is a contraction when the weight exceeds the Lipschitz rate. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorPicard (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : ℝ →ᵇ ℂ × ℂ) : ℝ →ᵇ ℂ × ℂ :=
  boundedRadialExteriorTail κ hκ (boundedRadialExteriorSource L C hL N hN hN0 hLip v)

theorem radialExteriorPicard_difference (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (u v : ℝ →ᵇ ℂ × ℂ) :
    ‖radialExteriorPicard κ L C hκ hL N hN hN0 hLip u-
      radialExteriorPicard κ L C hκ hL N hN hN0 hLip v‖ ≤ (L/κ)*‖u-v‖ := by
  calc
    _ ≤ ‖boundedRadialExteriorSource L C hL N hN hN0 hLip u-
      boundedRadialExteriorSource L C hL N hN hN0 hLip v‖/κ :=
        boundedRadialExteriorTail_difference κ hκ _ _
    _ ≤ (L*‖u-v‖)/κ := div_le_div_of_nonneg_right
      (boundedRadialExteriorSource_difference L C hL N hN hN0 hLip u v) hκ.le
    _ = _ := by ring

theorem radialExteriorPicard_contracting (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (hLκ : L < κ)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ContractingWith ⟨L/κ,div_nonneg hL hκ.le⟩ (radialExteriorPicard κ L C hκ hL N hN hN0 hLip) := by
  refine ⟨?_,LipschitzWith.of_dist_le_mul ?_⟩
  · change L/κ < 1
    exact (div_lt_one hκ).mpr hLκ
  · intro u v
    rw [dist_eq_norm,dist_eq_norm]
    exact radialExteriorPicard_difference κ L C hκ hL N hN hN0 hLip u v

theorem existsUnique_radialExteriorTail (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (hLκ : L < κ)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ∃! v : ℝ →ᵇ ℂ × ℂ, ∀ t,
      v t=radialExteriorTailIntegral κ (fun s => N s (v s)) t := by
  let P := radialExteriorPicard κ L C hκ hL N hN hN0 hLip
  have hP := radialExteriorPicard_contracting κ L C hκ hL hLκ N hN hN0 hLip
  refine ⟨hP.fixedPoint P,?_,?_⟩
  · intro t
    exact congrArg (fun w : ℝ →ᵇ ℂ × ℂ => w t) hP.fixedPoint_isFixedPt.symm
  · intro v hv
    apply hP.fixedPoint_unique
    apply BoundedContinuousFunction.ext
    intro t
    exact (hv t).symm

end DefocusingNLS

end OAI

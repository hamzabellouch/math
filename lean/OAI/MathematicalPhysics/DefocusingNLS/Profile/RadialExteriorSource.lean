import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailOperator

namespace OAI

/-! Bounded source fields and their pointwise action in the weighted tail space. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorSource_bound (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ)
    (hN0 : ∀ t, ‖N t 0‖ ≤ C)
    (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : ℝ →ᵇ ℂ × ℂ) (t : ℝ) : ‖N t (v t)‖ ≤ L*‖v‖+C := by
  calc
    _ ≤ ‖N t (v t)-N t 0‖+‖N t 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L*‖v t-0‖+C := add_le_add (hLip t _ _) (hN0 t)
    _ ≤ L*‖v‖+C := by
      rw [sub_zero]
      exact (add_le_add_iff_right C).mpr
        (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hL)

noncomputable def boundedRadialExteriorSource (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C)
    (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : ℝ →ᵇ ℂ × ℂ) : ℝ →ᵇ ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => N t (v t))
    (hN.comp (continuous_id.prodMk v.continuous)) (L*‖v‖+C)
    (radialExteriorSource_bound L C hL N hN0 hLip v)

theorem boundedRadialExteriorSource_norm (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C)
    (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : ℝ →ᵇ ℂ × ℂ) :
    ‖boundedRadialExteriorSource L C hL N hN hN0 hLip v‖ ≤ L*‖v‖+C := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  exact radialExteriorSource_bound L C hL N hN0 hLip v

theorem boundedRadialExteriorSource_difference (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C)
    (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (u v : ℝ →ᵇ ℂ × ℂ) :
    ‖boundedRadialExteriorSource L C hL N hN hN0 hLip u-
      boundedRadialExteriorSource L C hL N hN hN0 hLip v‖ ≤ L*‖u-v‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  change ‖N t (u t)-N t (v t)‖ ≤ L*‖u-v‖
  exact (hLip t _ _).trans (mul_le_mul_of_nonneg_left ((u-v).norm_coe_le_norm t) hL)

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailEquation

namespace OAI

/-! Stability of the actual backward integral equation under changes of its field. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_fixedPoint_difference
    (κ L K C D E : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hLκ : L < κ) (hE : 0 ≤ E)
    (N M : ℝ → (ℂ × ℂ) → ℂ × ℂ)
    (hN : Continuous (Function.uncurry N)) (hM : Continuous (Function.uncurry M))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hM0 : ∀ t, ‖M t 0‖ ≤ D)
    (hNL : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (hML : ∀ t z w, ‖M t z-M t w‖ ≤ K*‖z-w‖)
    (v w : ℝ →ᵇ ℂ × ℂ)
    (hv : ∀ t, v t=radialExteriorTailIntegral κ (fun s => N s (v s)) t)
    (hw : ∀ t, w t=radialExteriorTailIntegral κ (fun s => M s (w s)) t)
    (hNM : ∀ t, ‖N t (w t)-M t (w t)‖ ≤ E) :
    ‖v-w‖ ≤ E/(κ-L) := by
  let U := boundedRadialExteriorSource L C hL N hN hN0 hNL v
  let W := boundedRadialExteriorSource K D hK M hM hM0 hML w
  have hev : v=boundedRadialExteriorTail κ hκ U := by
    apply BoundedContinuousFunction.ext
    intro t
    exact hv t
  have hew : w=boundedRadialExteriorTail κ hκ W := by
    apply BoundedContinuousFunction.ext
    intro t
    exact hw t
  have hs : ‖U-W‖ ≤ L*‖v-w‖+E := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro t
    change ‖N t (v t)-M t (w t)‖ ≤ _
    calc
      _ ≤ ‖N t (v t)-N t (w t)‖+‖N t (w t)-M t (w t)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (N t (v t)) (N t (w t)) (M t (w t))
      _ ≤ L*‖v t-w t‖+E := add_le_add (hNL t _ _) (hNM t)
      _ ≤ L*‖v-w‖+E := by
        gcongr
        exact (v-w).norm_coe_le_norm t
  have hb : ‖v-w‖ ≤ (L*‖v-w‖+E)/κ := by
    calc
      _ = ‖boundedRadialExteriorTail κ hκ U-boundedRadialExteriorTail κ hκ W‖ := by rw [← hev,← hew]
      _ ≤ ‖U-W‖/κ := boundedRadialExteriorTail_difference κ hκ U W
      _ ≤ _ := div_le_div_of_nonneg_right hs hκ.le
  have hb' := (le_div_iff₀ hκ).mp hb
  apply (le_div_iff₀ (sub_pos.mpr hLκ)).mpr
  nlinarith

end DefocusingNLS

end OAI

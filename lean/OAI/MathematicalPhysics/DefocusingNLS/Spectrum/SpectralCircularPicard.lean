import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularSource

namespace OAI

/-! The coupled circular tail equation has a unique bounded weighted solution. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularPicard (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) : CircularTailSpace :=
  circularTail κ hκ (boundedCircularSource L C hL N hN hN0 hLip v)

theorem circularPicard_difference (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (u v : CircularTailSpace) :
    ‖circularPicard κ L C hκ hL N hN hN0 hLip u-
      circularPicard κ L C hκ hL N hN hN0 hLip v‖ ≤ (L/κ)*‖u-v‖ := by
  calc
    _ ≤ ‖boundedCircularSource L C hL N hN hN0 hLip u-
        boundedCircularSource L C hL N hN hN0 hLip v‖/κ := circularTail_difference κ hκ _ _
    _ ≤ (L*‖u-v‖)/κ := div_le_div_of_nonneg_right
      (boundedCircularSource_difference L C hL N hN hN0 hLip u v) hκ.le
    _ = _ := by ring

theorem circularPicard_contracting (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (hLκ : L < κ)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ContractingWith ⟨L/κ,div_nonneg hL hκ.le⟩ (circularPicard κ L C hκ hL N hN hN0 hLip) := by
  refine ⟨?_,LipschitzWith.of_dist_le_mul ?_⟩
  · change L/κ < 1
    exact (div_lt_one hκ).mpr hLκ
  · intro u v
    rw [dist_eq_norm,dist_eq_norm]
    exact circularPicard_difference κ L C hκ hL N hN hN0 hLip u v

theorem existsUnique_circularTail (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (hLκ : L < κ)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ∃! v : CircularTailSpace, circularPicard κ L C hκ hL N hN hN0 hLip v=v := by
  let P := circularPicard κ L C hκ hL N hN hN0 hLip
  have hP := circularPicard_contracting κ L C hκ hL hLκ N hN hN0 hLip
  exact ⟨hP.fixedPoint P,hP.fixedPoint_isFixedPt,fun _ hv => hP.fixedPoint_unique hv⟩

theorem circularTail_fixedPoint_bound (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (hLκ : L < κ) (hC : 0 ≤ C)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) (hv : circularPicard κ L C hκ hL N hN hN0 hLip v=v) :
    ‖v‖ ≤ C/(κ-L) := by
  have hb := circularTail_norm κ hκ (boundedCircularSource L C hL N hN hN0 hLip v)
  change ‖circularPicard κ L C hκ hL N hN hN0 hLip v‖ ≤ _ at hb
  rw [hv] at hb
  have hsource := boundedCircularSource_norm L C hL hC N hN hN0 hLip v
  have hh : κ*‖v‖ ≤ L*‖v‖+C := by
    have hh := (le_div_iff₀ hκ).mp (hb.trans (div_le_div_of_nonneg_right hsource hκ.le))
    nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hLκ)).mpr
  nlinarith

end DefocusingNLS

end OAI

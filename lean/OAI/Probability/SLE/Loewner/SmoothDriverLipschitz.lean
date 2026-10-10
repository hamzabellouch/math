import OAI.Probability.SLE.Loewner.SmoothRawInverse

namespace OAI

/-! A bounded derivative on nonnegative times gives a global Lipschitz
bound for the driver's constant extension to negative times. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem lipschitz_driverValue_of_bounded_derivative (b : Driver) (b' : ℝ → ℝ)
    (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) :
    LipschitzWith L (driverValue b) := by
  have hr : LipschitzOnWith L (driverValue b) (Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
    intro t ht
    exact_mod_cast (show ‖b' t‖ ≤ (L : ℝ) from by simpa only [Real.norm_eq_abs] using hb t ht)
  have hnn : LipschitzWith L b := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    simpa only [driverValue,Real.toNNReal_coe,NNReal.dist_eq,Real.dist_eq] using
      hr.dist_le_mul (t : ℝ) t.coe_nonneg (s : ℝ) s.coe_nonneg
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (b s.toNNReal) (b t.toNNReal) ≤ (L : ℝ)*dist s t
  exact (hnn.dist_le_mul _ _).trans (by
    simpa only [NNReal.coe_one,one_mul] using
      mul_le_mul_of_nonneg_left (Real.lipschitzWith_toNNReal.dist_le_mul s t) L.coe_nonneg)

end SLEExactGauge.Target

end

end OAI

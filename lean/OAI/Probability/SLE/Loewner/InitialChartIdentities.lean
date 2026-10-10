import OAI.Probability.SLE.Loewner.InitialForwardChart

namespace OAI

/-! Forward identities on the domain at the current time, rather than
only on the common final domain. -/
noncomputable section
open Set Function

namespace SLEExactGauge

lemma initialForwardChart_mem_upper (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    initialForwardChart p hi h0 hH s z∈upperHalfPlane := by
  by_cases hs : s=0
  · simpa only [hs,initialForwardChart_zero,id_eq] using hz.1
  · rw [initialForwardChart,dite_eq_right hs]
    exact (initialSlitChart p hi h0 hH s hs).bijOn.mapsTo hz

lemma initialInverse_forward_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    initialInverseChart p hi h0 hH s (initialForwardChart p hi h0 hH s z)=z := by
  by_cases hs : s=0
  · simp only [hs,initialForwardChart_zero,initialInverseChart_zero,id_eq]
  · rw [initialForwardChart,dite_eq_right hs,initialInverseChart,dite_eq_right hs]
    exact (initialSlitChart p hi h0 hH s hs).left_inverse z hz

end SLEExactGauge

end

end OAI

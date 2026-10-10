import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCommutatorSampling

namespace OAI

/-! # Uniform physical derivative commutators for sampled smooth potentials -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem torusProductCommutator_physical (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f : FourierL2) :
    torusFourierIsometry (expandingProductCommutator a L N ha ha1 hN hL j q f) =
      expandingOrderedPhysicalEnergy a L N hL j (expandingProduct a N L ha ha1 hN hL q f) -
        torusL2Product (expandingUnitTorusFunction a N L q)
          (expandingOrderedPhysicalEnergy a L N hL j f) := by
  change torusFourierIsometry (expandingOrderedFourierEnergy a L N hL j
      (expandingProduct a N L ha ha1 hN hL q f) -
      fourierConvolution (expandingFourierCoefficient a N L q)
        (expandingOrderedFourierEnergy a L N hL j f)) = _
  rw [map_sub, torusFourierIsometry_expanding_convolution a N L ha ha1 hN hL]
  rfl

theorem exists_schwartzProductCommutator_high_bound (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ)) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L), 1 ≤ R →
      ∀ (j : Fin (N + 1) → Fin 12) (f : FourierL2),
        (∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) →
      let q := schwartzTorusSample a ((N + 1 : ℕ) : ℝ) L ha1 hN hL K
      ‖expandingOrderedPhysicalEnergy a L (N + 1) hL j
          (expandingProduct a ((N + 1 : ℕ) : ℝ) L ha ha1 hN hL q f) -
        torusL2Product (expandingUnitTorusFunction a ((N + 1 : ℕ) : ℝ) L q)
          (expandingOrderedPhysicalEnergy a L (N + 1) hL j f)‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨D, hD, hDb⟩ := exists_schwartzCommutator_sampling_bound N K
  refine ⟨(N + 1 : ℕ) * D, by positivity, ?_⟩
  intro L R hL hR j f hf q
  obtain ⟨hs, hb⟩ := hDb L hL
  have hc : expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q = schwartzLatticeCoefficient L K := by
    funext n
    exact schwartzTorusSample_coefficient a ((N + 1 : ℕ) : ℝ) L ha1 hN hL K n
  have h := expandingProductCommutator_high_norm_le a L R N ha ha1 hN hL hR j q f
    (by simpa only [hc] using hs) hf
  rw [hc] at h
  rw [← torusProductCommutator_physical, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ((N + 1 : ℕ) / R) *
        (∑' m, expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) m) * ‖f‖ := h
    _ ≤ ((N + 1 : ℕ) / R) * D * ‖f‖ := by gcongr
    _ = _ := by ring

end DefocusingNLS

end OAI

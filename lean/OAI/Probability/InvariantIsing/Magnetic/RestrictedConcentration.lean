import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressure

namespace OAI

/-! The published SO(N) concentration input for every fixed nonempty
spin constraint, with constants independent of its cardinality. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

theorem haar_restricted_pressure_median_tail (hpub : HaarConcentrationInput) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ S : Finset (Spin N), S.Nonempty →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {U | restrictedRotatedPressure S eig (specialRotation U) c ≤ m} ∧
      (1 / 2 : ℝ) ≤ μ.real {U | m ≤ restrictedRotatedPressure S eig (specialRotation U) c} ∧
      ∀ r : ℝ, 0 < r →
        μ.real {U | r ≤ |restrictedRotatedPressure S eig (specialRotation U) c - m|} ≤
          C * Real.exp (-c₀ * (N : ℝ) * r ^ 2 / K ^ 2) := by
  obtain ⟨C, c₀, hC, hc, hp⟩ := hpub
  refine ⟨C, c₀, hC, hc, ?_⟩
  intro N hN μ hμ hμinv S hS eig c K hK heig
  exact hp N hN μ hμ hμinv _ (measurable_restrictedRotatedPressure S eig c) K hK
    (fun U V => abs_restrictedRotatedPressure_sub_rotation_le (by omega) S hS eig U V c K hK.le heig)

end InvariantIsing

end

end OAI

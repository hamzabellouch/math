import OAI.Probability.InvariantIsing.Pressure.PressureLipschitz

namespace OAI

/-!
# Haar concentration for Ising pressure

Frobenius Lipschitz continuity and measurability give concentration of the
Ising pressure about a median.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma measurable_specialRotation_eval {N : ℕ} (v : EuclideanSpace ℝ (Fin N))
    (i : Fin N) : Measurable (fun U : SpecialOrthogonal N => specialRotation U v i) := by
  simp only [specialRotation_apply]
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun U : SpecialOrthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact he.mul_const (v j)

lemma measurable_rotatedPressure {N : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c) := by
  have hE (σ : Spin N) : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul
        (eig i)).const_mul (1 / 2 : ℝ)).add_const _
  unfold rotatedPressure logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log.const_mul (N : ℝ)⁻¹

/-- Uniform concentration about a median for the actual spectral-orbit pressure,
conditional only on the cited concentration theorem. No pressure limit is an
assumption or a conclusion of this finite-volume estimate. -/
theorem haar_pressure_median_tail (hpub : HaarConcentrationInput) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {U | rotatedPressure eig (specialRotation U) c ≤ m} ∧
      (1 / 2 : ℝ) ≤ μ.real {U | m ≤ rotatedPressure eig (specialRotation U) c} ∧
      ∀ r : ℝ, 0 < r →
        μ.real {U | r ≤ |rotatedPressure eig (specialRotation U) c - m|} ≤
          C * Real.exp (-c₀ * (N : ℝ) * r ^ 2 / K ^ 2) := by
  obtain ⟨C, c₀, hC, hc, hp⟩ := hpub
  refine ⟨C, c₀, hC, hc, ?_⟩
  intro N hN μ hμ hμinv eig c K hK heig
  exact hp N hN μ hμ hμinv _ (measurable_rotatedPressure eig c) K hK
    (fun U V => abs_rotatedPressure_sub_rotation_le (by omega) eig U V c K hK.le heig)

end InvariantIsing

end

end OAI

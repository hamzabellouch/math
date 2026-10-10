import OAI.Probability.InvariantIsing.Arrays.NSpinComparison

namespace OAI

/-! Applying Haar concentration to the actual Gaussian cascade pressure. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_rotatedFieldTerminal_joint {N : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (Fin N → ℝ) =>
      rotatedFieldTerminal eig (specialRotation p.1) c p.2) := by
  have hE (σ : Spin N) : Measurable (fun p : SpecialOrthogonal N × (Fin N → ℝ) =>
      rotatedEnergy eig (specialRotation p.1) σ + fieldEnergy (c + p.2) σ) := by
    apply Measurable.add
    · exact (Finset.measurable_sum _ fun i _ =>
        (((measurable_specialRotation_eval (spinVector σ) i).comp measurable_fst).pow_const 2).const_mul
          (eig i)).const_mul (1 / 2 : ℝ)
    · unfold fieldEnergy
      fun_prop
  unfold rotatedFieldTerminal logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log

lemma measurable_rotatedCascadeValue_joint {N : ℕ} (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (eig c : Fin N → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (Fin N → ℝ) =>
      rotatedCascadeValue n b v eig (specialRotation p.1) c p.2) := by
  induction n generalizing b v with
  | zero => exact measurable_rotatedFieldTerminal_joint eig c
  | succ n ih =>
    have hp : Measurable (fun p : (SpecialOrthogonal N × (Fin N → ℝ)) × (Fin N → ℝ) =>
        (p.1.1, p.1.2 + p.2)) :=
      measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd)
    have hm := (((ih (fun i => b (i + 1)) (fun i => v (i + 1))).comp hp).const_mul (b 0)).exp
    exact hm.stronglyMeasurable.integral_prod_right.measurable.log.div_const (b 0)

lemma measurable_rotatedEnrichedPressure {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (root : ℝ≥0) (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnrichedPressure n b v root eig (specialRotation U) c) := by
  exact (measurable_rotatedCascadeValue_joint n b v eig c).stronglyMeasurable.integral_prod_right.measurable.const_mul (N : ℝ)⁻¹

/-- Uniform Haar tails for the finite enriched Ising pressure, conditional
only on the precise published concentration input. -/
theorem haar_enrichedPressure_median_tail (hpub : HaarConcentrationInput) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, ∀ v : ℕ → ℝ≥0, ∀ root : ℝ≥0,
      IsingPerceptron.CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {U | rotatedEnrichedPressure n b v root eig (specialRotation U) c ≤ m} ∧
      (1 / 2 : ℝ) ≤ μ.real {U | m ≤ rotatedEnrichedPressure n b v root eig (specialRotation U) c} ∧
      ∀ r : ℝ, 0 < r →
        μ.real {U | r ≤ |rotatedEnrichedPressure n b v root eig (specialRotation U) c - m|} ≤
          C * Real.exp (-c₀ * (N : ℝ) * r ^ 2 / K ^ 2) := by
  obtain ⟨C, c₀, hC, hc, hp⟩ := hpub
  refine ⟨C, c₀, hC, hc, ?_⟩
  intro N hN μ hμ hμinv n b v root hb eig c K hK heig
  exact hp N hN μ hμ hμinv _
    (measurable_rotatedEnrichedPressure n b v root eig c) K hK
    (fun U V => abs_rotatedEnrichedPressure_sub_rotation_le (by omega)
      n b v root hb eig U V c K hK.le heig)

end InvariantIsing

end

end OAI

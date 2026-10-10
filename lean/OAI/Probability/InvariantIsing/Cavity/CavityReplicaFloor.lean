import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerRegularization
import OAI.Probability.InvariantIsing.Cavity.CavityUnflooredLog

namespace OAI

/-! Removing the replica denominator regularizer using the same negative-log
moment that controls the logarithmic cavity partition function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_normalizer_log_error {A Z B δ : ℝ}
    (hZ : 0 < Z) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (r : ℕ)
    (hA : |A| ≤ B * Z ^ r) :
    |A / Z ^ r - A / (Z + δ) ^ r| ≤
      B * r * (Real.log (Z + δ) - Real.log Z) := by
  have hZd : 0 < Z + δ := add_pos_of_pos_of_nonneg hZ hδ
  let t := Z / (Z + δ)
  have ht : 0 < t := div_pos hZ hZd
  have ht1 : t ≤ 1 := (div_le_one hZd).mpr (by linarith)
  have htp : 0 ≤ 1 - t ^ r := sub_nonneg.mpr (pow_le_one₀ ht.le ht1)
  have he : A / Z ^ r - A / (Z + δ) ^ r = A / Z ^ r * (1 - t ^ r) := by
    dsimp [t]
    rw [div_pow]
    field_simp [hZ.ne', hZd.ne']
  have hlog : 1 - t ≤ Real.log (Z + δ) - Real.log Z := by
    have hh := Real.log_le_sub_one_of_pos ht
    dsimp only [t] at hh
    rw [Real.log_div hZ.ne' hZd.ne'] at hh
    linarith
  calc
    _ = |A / Z ^ r| * (1 - t ^ r) := by rw [he, abs_mul, abs_of_nonneg htp]
    _ ≤ B * (r * (1 - t)) :=
      mul_le_mul (cavity_normalized_numerator_bound hZ.le hB r hA)
        (cavity_one_sub_pow_le ht.le ht1 r) htp hB
    _ ≤ B * (r * (Real.log (Z + δ) - Real.log Z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg r)) hB
    _ = _ := by ring

lemma cavity_replica_floor_mean_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A Z : Ω → ℝ)
    (hA : Measurable A) (hZ : Measurable Z) {M B δ : ℝ}
    (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hB : 0 ≤ B)
    (hδ : 0 < δ) (r : ℕ) (hAZ : ∀ ω, |A ω| ≤ B * Z ω ^ r)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    |(∫ ω, A ω / Z ω ^ r ∂P) - (∫ ω, A ω / (Z ω + δ)^r ∂P)| ≤
      B * r * (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) := by
  have hiA : Integrable (fun ω => A ω / Z ω ^ r) P :=
    integrable_of_measurable_abs_le (hA.div (hZ.pow_const r))
      (fun ω => cavity_normalized_numerator_bound (hZ0 ω).le hB r (hAZ ω))
  have hiD : Integrable (fun ω => A ω / (Z ω + δ)^r) P :=
    integrable_of_measurable_abs_le (hA.div ((hZ.add_const δ).pow_const r))
      (fun ω => cavity_regularized_numerator_bound (hZ0 ω).le hB hδ.le r (hAZ ω))
  have hiL := (cavity_floored_log_integrable P Z hZ hZ0 hZM hδ).sub
    (cavity_log_integrable_of_negative_sq P Z hZ hZ0 hZM hi)
  rw [← integral_sub hiA hiD]
  calc
    _ ≤ ∫ ω, |A ω / Z ω ^ r - A ω / (Z ω + δ)^r| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, B * r * (Real.log (Z ω + δ) - Real.log (Z ω)) ∂P :=
      integral_mono (hiA.sub hiD).abs (hiL.const_mul (B * r))
        (fun ω => cavity_normalizer_log_error (hZ0 ω) hB hδ.le r (hAZ ω))
    _ = _ := integral_const_mul _ _

lemma cavity_replica_floor_uniform
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (A Z : (n : ℕ) → Ω n → ℝ) (hA : ∀ n, Measurable (A n))
    (hZ : ∀ n, Measurable (Z n)) {M B K : ℝ}
    (hM : 1 ≤ M) (hB : 0 ≤ B) (hK : 0 ≤ K) (r : ℕ)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hZM : ∀ n ω, Z n ω ≤ M)
    (hAZ : ∀ n ω, |A n ω| ≤ B * Z n ω ^ r)
    (hi : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hKi : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ n,
      |(∫ ω, A n ω / Z n ω ^ r ∂P n) -
        (∫ ω, A n ω / (Z n ω + δ)^r ∂P n)| < ε := by
  intro ε hε
  let C : ℝ := B * r
  have hC : 0 ≤ C := mul_nonneg hB (Nat.cast_nonneg r)
  let η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hCη : C * η < ε := by
    have he : (C + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨δ₀, hδ₀, hd⟩ := cavity_log_floor_uniform P Z hZ hZ0 hZM hM hK hi hKi η hη
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδbound n
  have hb := cavity_replica_floor_mean_error (P n) (A n) (Z n) (hA n) (hZ n)
    (hZ0 n) (hZM n) hB hδ r (hAZ n) (hi n)
  have hsmall := (hd δ ⟨hδ.le, hδbound⟩ n).2
  exact hb.trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsmall.le hC) hCη)

end InvariantIsing

end

end OAI

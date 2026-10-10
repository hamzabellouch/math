import OAI.NumberTheory.JointDickman.Amplification.SingleRegularityLoss
import OAI.NumberTheory.JointDickman.Arithmetic.SingleSieveMean

namespace OAI

/-! # Regularity loss for two independent coefficient weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularCoefficientWeight_le (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    regularCoefficientWeight B L τ C n ≤ coefficientWeight B n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact le_rfl
  · exact coefficientWeight_nonneg B n

theorem coefficient_truncation_loss_nonneg (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    0 ≤ coefficientWeight B n - regularCoefficientWeight B L τ C n :=
  sub_nonneg.mpr (regularCoefficientWeight_le B L τ C n)

theorem independent_truncation_loss_pointwise (B L : ℕ) (τ C : ℝ) (a b : ℕ) :
    coefficientWeight B a * coefficientWeight B b -
        regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b ≤
      (coefficientWeight B a - regularCoefficientWeight B L τ C a) * coefficientWeight B b +
        coefficientWeight B a * (coefficientWeight B b - regularCoefficientWeight B L τ C b) := by
  have h := mul_nonneg (coefficient_truncation_loss_nonneg B L τ C a)
    (coefficient_truncation_loss_nonneg B L τ C b)
  nlinarith only [h]

theorem independent_truncation_loss_sum (B L : ℕ) (τ C : ℝ) (I J : Finset ℕ) :
    (∑ a ∈ I, ∑ b ∈ J, (coefficientWeight B a * coefficientWeight B b -
        regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b)) ≤
      (∑ a ∈ I, (coefficientWeight B a - regularCoefficientWeight B L τ C a)) *
        (∑ b ∈ J, coefficientWeight B b) +
      (∑ a ∈ I, coefficientWeight B a) *
        (∑ b ∈ J, (coefficientWeight B b - regularCoefficientWeight B L τ C b)) := by
  calc
    _ ≤ ∑ a ∈ I, ∑ b ∈ J,
        ((coefficientWeight B a - regularCoefficientWeight B L τ C a) * coefficientWeight B b +
          coefficientWeight B a * (coefficientWeight B b - regularCoefficientWeight B L τ C b)) := by
      exact sum_le_sum fun a _ => sum_le_sum fun b _ =>
        independent_truncation_loss_pointwise B L τ C a b
    _ = _ := by
      simp only [sum_add_distrib, sum_mul, mul_sum]
      congr 1 <;> apply sum_comm

/-- The independent two-variable assertion of the manuscript's regularity-loss lemma: the
loss is bounded by the area, uniformly in the tail cutoff. The two inputs
are the cited upper sieve and reciprocal-prime Mertens estimate. -/
theorem independent_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (u v x y : ℕ), 0 ≤ C → u ≤ v → x ≤ y →
          Real.exp (δ * B) ≤ (v : ℝ) - u → Real.exp (δ * B) ≤ (y : ℝ) - x →
          (∑ a ∈ Ico u v, ∑ b ∈ Ico x y, (coefficientWeight B a * coefficientWeight B b -
            regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b)) ≤
            K * ((v : ℝ) - u) * ((y : ℝ) - x) * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hloss⟩ := single_coefficient_regularity_loss hFord hM hδ hδ32
  obtain ⟨M, hM0, hmean⟩ := single_coefficient_mean_bound hFord hM hδ
  refine ⟨2 * K * M, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hloss L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, hmean] with B hl hm
  intro C u v x y hC huv hxy huvlen hxylen
  have hu := hl C u v hC huv huvlen
  have hx := hl C x y hC hxy hxylen
  have hmu := hm u v huv huvlen
  have hmx := hm x y hxy hxylen
  have hu0 : 0 ≤ ∑ a ∈ Ico u v, coefficientWeight B a :=
    sum_nonneg fun a _ => coefficientWeight_nonneg B a
  have hx0 : 0 ≤ ∑ b ∈ Ico x y, coefficientWeight B b :=
    sum_nonneg fun b _ => coefficientWeight_nonneg B b
  have hdx0 : 0 ≤ ∑ b ∈ Ico x y, (coefficientWeight B b - regularCoefficientWeight B L τ C b) :=
    sum_nonneg fun b _ => coefficient_truncation_loss_nonneg B L τ C b
  have hU : 0 ≤ (v : ℝ) - u := (Real.exp_pos _).le.trans huvlen
  have hX : 0 ≤ (y : ℝ) - x := (Real.exp_pos _).le.trans hxylen
  have hF : 0 ≤ ε B + Real.exp (-(1 / 10 : ℝ) * C) := add_nonneg (hε0 B) (Real.exp_pos _).le
  have h1 := mul_le_mul hu hmx hx0 (mul_nonneg (mul_nonneg hK.le hU) hF)
  have h2 := mul_le_mul hmu hx hdx0 (mul_nonneg hM0.le hU)
  calc
    _ ≤ _ := independent_truncation_loss_sum B L τ C (Ico u v) (Ico x y)
    _ ≤ (K * ((v : ℝ) - u) * (ε B + Real.exp (-(1 / 10 : ℝ) * C))) * (M * ((y : ℝ) - x)) +
        (M * ((v : ℝ) - u)) * (K * ((y : ℝ) - x) * (ε B + Real.exp (-(1 / 10 : ℝ) * C))) :=
      add_le_add h1 h2
    _ = _ := by ring

end JointDickman

end OAI

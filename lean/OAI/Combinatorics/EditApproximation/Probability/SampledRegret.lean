import OAI.Combinatorics.EditApproximation.Geometry.ChildIncrements
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import OAI.Combinatorics.EditApproximation.Probability.FiniteSampling

namespace OAI

/-!
# Exact sampled action costs

The sampler's finite law translates the computed rational vector into its
expected linear cost. Correlation with a group-estimation failure is not
excluded or needed in this identity.
-/

namespace EditApproximation

open Finset

theorem uniformMean_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uniformMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω => f ω + g ω) = uniformMean f + uniformMean g := by
  simp only [uniformMean, sum_add_distrib, add_div]

theorem uniformMean_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω => a * f ω) = a * uniformMean f := by
  simp only [uniformMean, ← mul_sum, mul_div_assoc]

theorem uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by
  simp only [uniformMean, sum_const, card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ a hcard

theorem uniformMean_sum {Ω ι : Type*} [Fintype Ω] (indices : Finset ι) (f : ι → Ω → ℝ) :
    uniformMean (fun ω => ∑ i ∈ indices, f i ω) = ∑ i ∈ indices, uniformMean (f i) := by
  unfold uniformMean
  rw [sum_comm, sum_div]

theorem finiteRationalOptimizer_sampler_linear_mean {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (linear : ι → ℚ)
    (G K : ℕ) (hK : 0 < K) (payoff : ι → ℝ) :
    let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hK)⟩
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      ∑ i ∈ coordinates, payoff i *
        (finiteOptimizerSelection coordinates vertices linear G (triangularChoice K integer).val i : ℝ)) =
      ∑ i ∈ coordinates, payoff i * (finiteRationalOptimizer coordinates vertices linear G K i : ℝ) := by
  let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hK)⟩
  dsimp only
  unfold uniformMean
  rw [Fintype.card_fin, sum_comm, sum_div]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum, mul_div_assoc]
  congr 1
  have hmean := finiteRationalOptimizer_sampler_mean coordinates vertices linear G K hK i
  exact_mod_cast hmean

theorem actionVector_child_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ)
    {action : β → σ} (ha : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ i ∈ bandCoordinates band,
        ((childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i) *
          (actionVector mass action i : ℝ)) =
      (∑ child, (table (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (table t (child, action child) : ℝ)) -
          ∑ child, (table (t + 1) (child, action child) : ℝ)) := by
  have hidentity := actionVector_cost_identity band mass hpos
    (fun i => (κ : ℝ) * table t i + (1 - (κ : ℝ)) * table (t + 1) i) ha
  have hgain i : (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i =
      -((κ : ℝ) * table t i + (1 - (κ : ℝ)) * table (t + 1) i) / (mass i.1 : ℝ) := by
    have hid := childGain_decrement_identity mass table κ t i
    exact_mod_cast hid
  simp_rw [hgain]
  rw [hidentity]
  simp only [sum_add_distrib, ← mul_sum]
  ring

theorem actionVector_comparator_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (t : ℕ)
    {action : β → σ} (ha : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ i ∈ bandCoordinates band,
        ((childGain mass table t i : ℝ) + childDecrement mass table t i) *
          (actionVector mass action i : ℝ)) =
      ∑ child, (table (t + 1) (child, action child) : ℝ) := by
  simpa only [Rat.cast_zero, sub_zero, one_mul, zero_mul, add_zero] using
    actionVector_child_cost_identity band mass hpos table 0 t ha

end EditApproximation

end OAI

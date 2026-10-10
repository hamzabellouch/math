import OAI.NumberTheory.TwoPointCorrelations.CRTComparison
import OAI.NumberTheory.TwoPointCorrelations.FiniteProbability

namespace OAI

/-! Exact residue laws for one interval and three independent intervals.
The box discrepancy is derived by tensoring the one-dimensional count,
without estimating each individual three-dimensional residue atom. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finiteTotalVariation_product {α β : Type*} [Fintype α] [Fintype β]
    (μ₁ ν₁ : FiniteLaw α) (μ₂ ν₂ : FiniteLaw β) :
    finiteTotalVariation (μ₁.product μ₂).weight (ν₁.product ν₂).weight ≤
      finiteTotalVariation μ₁.weight ν₁.weight + finiteTotalVariation μ₂.weight ν₂.weight := by
  have hpoint (x : α) (y : β) :
      |μ₁.weight x * μ₂.weight y - ν₁.weight x * ν₂.weight y| ≤
        |μ₁.weight x - ν₁.weight x| * μ₂.weight y +
          ν₁.weight x * |μ₂.weight y - ν₂.weight y| := by
    calc
      _ = |(μ₁.weight x - ν₁.weight x) * μ₂.weight y +
          ν₁.weight x * (μ₂.weight y - ν₂.weight y)| := by congr 1; ring
      _ ≤ |(μ₁.weight x - ν₁.weight x) * μ₂.weight y| +
          |ν₁.weight x * (μ₂.weight y - ν₂.weight y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (μ₂.nonneg y),
        abs_of_nonneg (ν₁.nonneg x)]
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) =>
    sum_le_sum (fun y (_ : y ∈ (univ : Finset β)) => hpoint x y))
  have heq : (∑ x : α, ∑ y : β,
      (|μ₁.weight x - ν₁.weight x| * μ₂.weight y +
        ν₁.weight x * |μ₂.weight y - ν₂.weight y|)) =
      (∑ x, |μ₁.weight x - ν₁.weight x|) +
        ∑ y, |μ₂.weight y - ν₂.weight y| := by
    simp only [sum_add_distrib, ← mul_sum, μ₂.total, mul_one]
    rw [← sum_mul, ν₁.total, one_mul]
  rw [heq] at hsum
  unfold finiteTotalVariation
  simp only [FiniteLaw.product, Fintype.sum_prod_type]
  exact (div_le_div_of_nonneg_right hsum (by norm_num)).trans_eq (add_div _ _ 2)

noncomputable def uniformZModLaw (D : ℕ) [NeZero D] : FiniteLaw (ZMod D) where
  weight _ := 1 / D
  nonneg _ := by positivity
  total := by simp [ZMod.card, nsmul_eq_mul, NeZero.ne D]

noncomputable def intervalResidueLaw {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) : FiniteLaw (ZMod D) where
  weight := residueProbability A N
  nonneg _ := by unfold residueProbability; positivity
  total := residueProbability_sum A N hN

lemma intervalResidueLaw_totalVariation {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) :
    finiteTotalVariation (intervalResidueLaw A N hN).weight (uniformZModLaw D).weight ≤
      (D : ℝ) / (2 * N) :=
  residueTotalVariation_le A N hN

/-- The residue mass is the exact pushforward of uniform interval sampling. -/
lemma intervalResidueLaw_average {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      (∑ j ∈ range N, f (A + (j : ZMod D))) / N := by
  unfold FiniteLaw.average intervalResidueLaw residueProbability residueCount
  simp only [div_mul_eq_mul_div, ← sum_div, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [ite_mul, one_mul, zero_mul]
  simp

noncomputable def residueCubeLaw {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N) :
    FiniteLaw (ZMod D × ZMod D × ZMod D) :=
  (intervalResidueLaw A.1 N hN).product
    ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))

noncomputable def uniformResidueCubeLaw (D : ℕ) [NeZero D] :
    FiniteLaw (ZMod D × ZMod D × ZMod D) :=
  (uniformZModLaw D).product ((uniformZModLaw D).product (uniformZModLaw D))

theorem residueCube_totalVariation {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N) :
    finiteTotalVariation (residueCubeLaw A N hN).weight (uniformResidueCubeLaw D).weight ≤
      3 * D / (2 * (N : ℝ)) := by
  have h₁ := intervalResidueLaw_totalVariation A.1 N hN
  have h₂ := intervalResidueLaw_totalVariation A.2.1 N hN
  have h₃ := intervalResidueLaw_totalVariation A.2.2 N hN
  have h₂₃ := finiteTotalVariation_product
    (intervalResidueLaw A.2.1 N hN) (uniformZModLaw D)
    (intervalResidueLaw A.2.2 N hN) (uniformZModLaw D)
  have h₁₂₃ := finiteTotalVariation_product
    (intervalResidueLaw A.1 N hN) (uniformZModLaw D)
    ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))
    ((uniformZModLaw D).product (uniformZModLaw D))
  change finiteTotalVariation
    ((intervalResidueLaw A.1 N hN).product
      ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))).weight
    ((uniformZModLaw D).product ((uniformZModLaw D).product (uniformZModLaw D))).weight ≤ _
  calc
    _ ≤ 3 * ((D : ℝ) / (2 * N)) := by linarith
    _ = _ := by ring

/-- Any simultaneous collection of congruence conditions has the same
`3D/N` box error; the number of allowed residue vectors is irrelevant. -/
theorem residueCube_probability_discrepancy {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N)
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    |(residueCubeLaw A N hN).probability E - (uniformResidueCubeLaw D).probability E| ≤
      3 * D / (N : ℝ) := by
  have hb := finite_observable_difference (residueCubeLaw A N hN).weight
    (uniformResidueCubeLaw D).weight (fun x => if E x then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have hv := residueCube_totalVariation A N hN
  change |(residueCubeLaw A N hN).probability E -
    (uniformResidueCubeLaw D).probability E| ≤ _ at hb
  calc
    _ ≤ 2 * finiteTotalVariation (residueCubeLaw A N hN).weight
        (uniformResidueCubeLaw D).weight := hb
    _ ≤ 2 * (3 * D / (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

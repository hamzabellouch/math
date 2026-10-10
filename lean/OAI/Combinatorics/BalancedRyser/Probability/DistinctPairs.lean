import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Candidates.ConstituentOffsets

namespace OAI

open Filter
open scoped Topology
open scoped Classical

namespace Balanced
open scoped _root_.Balanced

noncomputable section

theorem card_distinct_pairs (K : Type*) [Fintype K] :
    Fintype.card {p : K × K // p.1 ≠ p.2} =
      Fintype.card K * (Fintype.card K - 1) := by
  classical
  let e : {p : K × K // p.1 ≠ p.2} ≃ (Σ x : K, {y : K // y ≠ x}) :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Ne.symm p.2⟩
      invFun := fun p => ⟨(p.1, p.2.1), Ne.symm p.2.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp

theorem card_allConstituentPairsDistinct (D K : Type*) [Fintype D] [Fintype K] :
    Fintype.card {M : ConstituentOffsets D K // AllConstituentPairsDistinct M} =
      (Fintype.card K * (Fintype.card K - 1)) ^ Fintype.card D := by
  classical
  let e : {M : ConstituentOffsets D K // AllConstituentPairsDistinct M} ≃
      (D → {p : K × K // p.1 ≠ p.2}) :=
    { toFun := fun M d => ⟨M.1 d, M.2 d⟩
      invFun := fun M => ⟨fun d => (M d).1, fun d => (M d).2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  calc
    _ = Fintype.card (D → {p : K × K // p.1 ≠ p.2}) := Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_fun]
      exact congrArg (fun n => n ^ Fintype.card D) (card_distinct_pairs K)

theorem finiteUniformProbability_eq_toOuterMeasure {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (E : Ω → Prop) :
    finiteUniformProbability E =
      ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [finiteUniformProbability, ENNReal.toReal_div, ENNReal.toReal_natCast,
    Fintype.card_eq_nat_card]
  rfl

theorem distinctConstituentProbability_eq (q : ℕ) (hq : 0 < q) :
    distinctConstituentProbability q = (1 - 1 / (q : ℝ)) ^ (q + 1) := by
  unfold distinctConstituentProbability finiteUniformProbability
  have hc := card_allConstituentPairsDistinct (Fin (q + 1)) (Fin q)
  rw [Fintype.card_eq_nat_card] at hc
  rw [hc]
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_mul]
  rw [← div_pow]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem tendsto_distinctConstituentProbability :
    Tendsto distinctConstituentProbability atTop (𝓝 (Real.exp (-1))) := by
  have h₁ : Tendsto (fun q : ℕ => 1 - 1 / (q : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h₂ : Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ q)
      atTop (𝓝 (Real.exp (-1))) := by
    simpa only [neg_div, one_div, sub_eq_add_neg] using
      Real.tendsto_one_add_div_pow_exp (-1)
  have h := h₂.mul h₁
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [distinctConstituentProbability_eq q (by omega), pow_succ]

end
end Balanced

end OAI

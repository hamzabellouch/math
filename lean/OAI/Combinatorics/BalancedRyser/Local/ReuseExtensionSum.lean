import OAI.Combinatorics.BalancedRyser.Local.ReuseTargetSum
import OAI.Combinatorics.BalancedRyser.Probability.GeneratorEnumeration

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem cyclic_index_ne_next (i : Fin 4) : i ≠ i + 1 := by
  have h : ∀ i : Fin 4, i ≠ i + 1 := by decide
  exact h i

def tupleCodeTargetMass (old : Finset (Direction F)) (M : MergedPairs F)
    (p : Point F) (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) : ℝ :=
  if hinj : Function.Injective c.1 then
    ∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, c.1 i ≠ g)),
      externalAlignmentProbability c.1
        (fun i h => cyclic_index_ne_next i (hinj h)) c.2 p g
        (oldGeneratorIndices ⟨c.1, c.2⟩ old) (fun i => M (c.1 i))
  else 0

theorem tupleCodeTargetMass_scaled_le (old : Finset (Direction F))
    (M : MergedPairs F) (p : Point F)
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) (j : ℕ)
    (hc : c ∈ tupleCodesWithOldCount old j) (K : ℝ) (hK : 0 ≤ K) :
    (Fintype.card F : ℝ) ^ (4 - j) * tupleCodeTargetMass old M p c *
      (K / Fintype.card F) ≤ 2 * K / (Fintype.card F : ℝ) ^ reuseSaving j := by
  obtain ⟨hgen, _⟩ := Finset.mem_product.mp hc
  have hJ : (oldGeneratorIndices (⟨c.1, c.2⟩ : FourTuple F) old).card = j :=
    (Finset.mem_filter.mp hgen).2
  unfold tupleCodeTargetMass
  split_ifs with hinj
  · simpa only [hJ] using scaled_sum_externalAlignmentProbability_le c.1
      (fun i h => cyclic_index_ne_next i (hinj h)) c.2 p
      (oldGeneratorIndices ⟨c.1, c.2⟩ old) (fun i => M (c.1 i)) K hK
  · simp only [mul_zero, zero_mul]
    positivity

theorem sum_tupleCodeTargetMass_extension_le (old : Finset (Direction F))
    (M : MergedPairs F) (p : Point F) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) (K : ℝ) (hK : 0 ≤ K) :
    2 * (∑ c ∈ tupleCodesWithOldCount old j,
      tupleCodeTargetMass old M p c * (K / Fintype.card F)) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by
    change (0 : ℝ) < (Fintype.card F : ℝ)
    exact_mod_cast Fintype.card_pos (α := F)
  have hqpow : 0 < q ^ (4 - j) := pow_pos hq _
  have hcount : ((tupleCodesWithOldCount old j).card : ℝ) ≤
      (4096 * 24 ^ 4 : ℝ) * q ^ (4 - j) := by
    dsimp [q]
    exact_mod_cast card_tupleCodesWithOldCount_le_field old j hold hj
  have hscaled :
      q ^ (4 - j) * (∑ c ∈ tupleCodesWithOldCount old j,
        tupleCodeTargetMass old M p c * (K / q)) ≤
        (4096 * 24 ^ 4 : ℝ) * q ^ (4 - j) * (2 * K / q ^ reuseSaving j) := by
    calc
      q ^ (4 - j) * (∑ c ∈ tupleCodesWithOldCount old j,
          tupleCodeTargetMass old M p c * (K / q)) =
        ∑ c ∈ tupleCodesWithOldCount old j,
          q ^ (4 - j) * tupleCodeTargetMass old M p c * (K / q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ ∑ _c ∈ tupleCodesWithOldCount old j, 2 * K / q ^ reuseSaving j := by
        apply Finset.sum_le_sum
        intro c hc
        exact tupleCodeTargetMass_scaled_le old M p c j hc K hK
      _ = ((tupleCodesWithOldCount old j).card : ℝ) * (2 * K / q ^ reuseSaving j) := by
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)
  have hsingle :
      (∑ c ∈ tupleCodesWithOldCount old j,
        tupleCodeTargetMass old M p c * (K / q)) ≤
        (4096 * 24 ^ 4 : ℝ) * (2 * K / q ^ reuseSaving j) := by
    apply (mul_le_mul_iff_right₀ hqpow).mp
    nlinarith [hscaled]
  change 2 * (∑ c ∈ tupleCodesWithOldCount old j,
    tupleCodeTargetMass old M p c * (K / q)) ≤ _
  calc
    _ ≤ 2 * ((4096 * 24 ^ 4 : ℝ) * (2 * K / q ^ reuseSaving j)) := by
      gcongr
    _ = _ := by ring

end
end Balanced

end OAI

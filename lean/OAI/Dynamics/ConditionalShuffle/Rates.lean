import OAI.Dynamics.ConditionalShuffle.CanonicalBridge

namespace OAI

noncomputable section
open Filter Topology
namespace Thorp.Conditional
open scoped Classical
open Revealed.Split Revealed.Disintegration

def conditionalRate (d : ℕ) : ℝ :=
  Real.sqrt (12544 * ((1 / 32 : ℝ) ^ d + (2 ^ d : ℝ) ^ 3 * (9 / 10 : ℝ) ^ (2 ^ d)))

lemma conditionalRate_tendsto : Tendsto conditionalRate atTop (nhds 0) := by
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
  have h₂ := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hh := ((h₁.add h₂).const_mul 12544).sqrt
  unfold conditionalRate
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Function.comp_def,
    add_zero, mul_zero, Real.sqrt_zero] using hh

lemma frameJoint_sum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) : ∑ z, frameJoint L t z = 1 := fairMass_sum _

lemma frameMarginal_sum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) : ∑ p, marginal (frameJoint L t) p = 1 := by
  rw [marginal_sum, frameJoint_sum]

lemma frameKernel_marginal_rate {ι : Type*} [Fintype ι] (d : ℕ)
    (L : Sum ι (Position (d + 1 + 2)) ≃ Position (d + 2 + 2))
    (e : Fin (7 * 2 ^ d) → Position (d + 1 + 2)) (he : Function.Injective e) :
    (∑ p, marginal (frameJoint L (400 * (d + 2 + 2))) p *
      tv (Trim.push (frameKernel L (400 * (d + 2 + 2)) p) (fun g => g ∘ e))
        (fairMass (fun g : State (d + 1 + 2) => g ∘ e))) ≤ conditionalRate d := by
  have hc : Fintype.card (Position (d + 2 + 2)) = 16 * 2 ^ d := by
    simp only [card_position, pow_add]
    norm_num
    omega
  have hf : Fintype.card (Position (d + 1 + 2)) = 8 * 2 ^ d := by
    simp only [card_position, pow_add]
    norm_num
    omega
  have hh := frameKernel_marginal_400 (d + 2) (2 ^ d) (by rw [hc]) L (7 * 2 ^ d)
    (by rw [hf]; omega) e he
  apply hh.trans
  unfold conditionalRate
  apply Real.le_sqrt_of_sq_le
  have hp : (1 / 2 : ℝ) ^ (8 * (d + 2 + 2)) ≤ (1 / 2 : ℝ) ^ (8 * d) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hid : (2 ^ d : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (8 * d) = (1 / 32 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 3, pow_mul, pow_mul, ← mul_pow]
    norm_num
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (2 ^ d : ℝ) ^ 3)
  rw [hid] at hp'
  have hsq :
      (((7 * 2 ^ d : ℕ) : ℝ) / 2 *
        Real.sqrt ((Fintype.card (Position (d + 2 + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 2 + 2)) + 64 * (9 / 10 : ℝ) ^ (2 ^ d)))) ^ 2 =
      196 * (2 ^ d : ℝ) ^ 3 *
        ((1 / 2 : ℝ) ^ (8 * (d + 2 + 2)) + 64 * (9 / 10 : ℝ) ^ (2 ^ d)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hc]
    push_cast
    ring
  rw [hsq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) d]

lemma average_discarded_le {ι : Type*} [Fintype ι] (d : ℕ)
    (L : Sum ι (Position (d + 1 + 2)) ≃ Position (d + 2 + 2)) :
    (∑ p, marginal (frameJoint L (400 * (d + 2 + 2))) p *
      Trim.discarded (Block.embedding (Block.eightEquiv d)) (frameKernel L (400 * (d + 2 + 2)) p)) ≤
        16 * conditionalRate d := by
  let T := 400 * (d + 2 + 2)
  let q := marginal (frameJoint L T)
  let μ := frameKernel L T
  have hp (p) := Block.discarded_ordered_bound (Block.eightEquiv d) (Block.ordering d) (μ p)
    (frameKernel_nonneg L T p) (frameKernel_sum L T p)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hp p) (marginal_nonneg _ (frameJoint_nonneg L T) p))
  have hu (i : Fin 8) :
      Trim.push (fun _ : State (d+1+2) => (Fintype.card (State (d+1+2)) : ℝ)⁻¹)
        (Block.orderedRestriction (Block.eightEquiv d) i (Block.ordering d i)) =
      fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i) := Block.push_uniform_ordered d i
  simp only [hu] at hb
  change (∑ p, q p * Trim.discarded _ (μ p)) ≤
    ∑ p, q p * (2 * ∑ i, tv (Trim.push (μ p) (fun g => g ∘ Block.domain d i))
      (fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i))) at hb
  have hswap : (∑ p, q p * (2 * ∑ i, tv (Trim.push (μ p) (fun g => g ∘ Block.domain d i))
      (fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i)))) =
      2 * ∑ i, ∑ p, q p * tv (Trim.push (μ p) (fun g => g ∘ Block.domain d i))
        (fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hswap] at hb
  have hi (i : Fin 8) := frameKernel_marginal_rate d L (Block.domain d i) (Block.domain_injective d i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  dsimp only [q, μ, T] at hb
  norm_num only [Nat.cast_ofNat] at hs
  exact hb.trans (by linarith)

end Thorp.Conditional

end

end OAI

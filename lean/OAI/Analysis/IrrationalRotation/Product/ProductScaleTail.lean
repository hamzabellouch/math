import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Sampling.BlockPhaseConstruction

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

open ProductPhases InvariantProjection.IndependentAngles
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

omit hp

theorem mem_consecutiveBlock_tail (j r i : ℕ)
    (hi : i ∈ consecutiveBlock (fun k => p.m (j + k)) r) :
    p.prefixCount j + i ∈ consecutiveBlock p.m (j + r) := by
  have h := (mem_consecutiveBlock_iff _ _ _).mp hi
  apply (mem_consecutiveBlock_iff _ _ _).mpr
  rw [Finset.sum_range_add]
  dsimp [ProductScaleData.prefixCount]
  omega

include hp

theorem angle_tail_le (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (j : ℕ) :
    (∑' i, θ (p.prefixCount j + i)) ≤ 2 * (∑' r, 1 / (p.K (j + r) : ℝ)) := by
  let mt : ℕ → ℕ := fun r => p.m (j + r)
  let Kt : ℕ → ℝ := fun r => p.K (j + r)
  have hm : ∀ r, 0 < mt r := fun r => hp.m_pos (j + r)
  have hK : ∀ r, 0 < Kt r := fun r => hp.real_K_pos (j + r)
  have hsum : Summable (fun r => 1 / Kt r) := by
    simpa only [Kt, Nat.add_comm] using (summable_nat_add_iff j).mpr hp.summable_reciprocal
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv mt hm
  have hrec := enumerated_block_reciprocal mt hm Kt hK hsum e
  have hbound (i : ℕ) : θ (p.prefixCount j + i) ≤
      2 * (1 / ((mt (e i).1 : ℝ) * Kt (e i).1)) := by
    have hi := mem_consecutiveBlock_enumeration mt e he i
    have hi' := mem_consecutiveBlock_tail j (e i).1 i hi
    simpa only [mt, Kt, mul_one_div] using hθ _ _ hi'
  have hs : Summable (fun i => θ (p.prefixCount j + i)) :=
    Summable.of_nonneg_of_le (fun i => hθ0 _) hbound (hrec.1.mul_left 2)
  calc
    _ ≤ ∑' i, 2 * (1 / ((mt (e i).1 : ℝ) * Kt (e i).1)) :=
      hs.tsum_le_tsum hbound (hrec.1.mul_left 2)
    _ = 2 * (∑' r, 1 / (p.K (j + r) : ℝ)) := by
      rw [tsum_mul_left, hrec.2]

theorem angle_tail_le_four_div_next (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (n : ℕ) :
    (∑' i, θ (p.prefixCount (n + 1) + i)) ≤ 4 / (p.K (n + 1) : ℝ) := by
  calc
    _ ≤ 2 * (∑' r, 1 / (p.K (n + 1 + r) : ℝ)) := hp.angle_tail_le θ hθ0 hθ (n + 1)
    _ ≤ 2 * (2 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound n) (by norm_num)
    _ = _ := by ring

theorem horizon_ratio_le_decay (n : ℕ) :
    (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) / p.K (n + 1) ≤
      (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20) := by
  have hm : 0 < (p.m n : ℝ) := by exact_mod_cast hp.m_pos n
  have hnext : (p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n) ≤ p.K (n + 1) := by
    rw [hp.next_K n]
    exact Nat.le_ceil _
  calc
    _ ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) /
        (p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hm _) hnext
    _ = _ := by rw [← Real.rpow_sub hm]; congr 1; ring

theorem power_mul_angle_tail_le (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (n t : ℕ)
    (ht : (t : ℝ) ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n)) :
    (t : ℝ) * (∑' i, θ (p.prefixCount (n + 1) + i)) ≤
      4 * (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20) := by
  calc
    _ ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) * (4 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul ht (hp.angle_tail_le_four_div_next θ hθ0 hθ n)
        (tsum_nonneg fun _ => hθ0 _) (by positivity)
    _ = 4 * ((p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) / p.K (n + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.horizon_ratio_le_decay n) (by norm_num)

theorem tendsto_tail_trim_bound :
    Tendsto (fun n => 4 * (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20)) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => (p.m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp.m_strictMono.tendsto_atTop
  have hi : Tendsto (fun n => 4 * (p.m n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hm).const_mul 4
  apply squeeze_zero' _ _ hi
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · apply Filter.Eventually.of_forall
    intro n
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply SamplingHorizon.decay_le_inv
    exact_mod_cast le_trans (by decide : 20 ≤ 100) (hp.m_ge_100 n)

end Invariant233.ProductScaleLaws

end

end OAI

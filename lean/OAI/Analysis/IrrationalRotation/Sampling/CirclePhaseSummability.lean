import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterConsequences
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_sum_le (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.alpha θ i) ≤ 2 / (p.K j : ℝ) := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    (∑ i ∈ p.block j, p.alpha θ i) ≤ ∑ i ∈ p.block j, 2 / p.N j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).2.le
    _ = ((p.block j).card : ℝ) * (2 / p.N j) := by simp
    _ = 2 / (p.K j : ℝ) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp

theorem block_phase_sum_lower (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.K j : ℝ) ≤ ∑ i ∈ p.block j, p.alpha θ i := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    1 / (p.K j : ℝ) = ((p.block j).card : ℝ) * (1 / p.N j) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp
    _ = ∑ i ∈ p.block j, 1 / p.N j := by simp
    _ ≤ ∑ i ∈ p.block j, p.alpha θ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).1.le

theorem one_le_block_log_cost (j : ℕ) (hj : 1 ≤ j) :
    1 ≤ p.C j * ∑ i ∈ p.block j, p.alpha θ i := by
  have hK : 0 < (p.K j : ℝ) := by exact_mod_cast hp.K_pos j hj
  have hK1 : 1 ≤ (p.K j : ℝ) := by exact_mod_cast hp.K_pos j hj
  have hC : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j hj]
    exact le_max_right _ _
  calc
    1 ≤ (p.K j : ℝ) := hK1
    _ ≤ p.C j / (p.K j : ℝ) := by
      apply (le_div_iff₀ hK).mpr
      nlinarith
    _ = p.C j * (1 / (p.K j : ℝ)) := by ring
    _ ≤ p.C j * ∑ i ∈ p.block j, p.alpha θ i :=
      mul_le_mul_of_nonneg_left (hp.block_phase_sum_lower j hj) (hp.C_pos j hj).le

theorem tsum_block_log_cost_eq_top :
    (∑' n : ℕ, ENNReal.ofReal
      (p.C (n + 1) * ∑ i ∈ p.block (n + 1), p.alpha θ i)) = ∞ := by
  apply top_unique
  calc
    (∞ : ENNReal) = ∑' _ : ℕ, (1 : ENNReal) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (p.C (n + 1) * ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (hp.one_le_block_log_cost (n + 1) (by omega))

theorem summable_block_phases :
    Summable (fun n : ℕ => ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg (fun i _ => Int.fract_nonneg _))
    (fun n => hp.block_phase_sum_le (n + 1) (by omega))
  simpa only [mul_one_div] using hp.summable_reciprocal.mul_left 2

private def blocksWithZero (p : CircleParameterData) (j : ℕ) : Finset ℕ :=
  if j = 0 then {0} else p.block j

private theorem blocksWithZero_partition :
    ∀ i : ℕ, ∃! j : ℕ, i ∈ blocksWithZero p j := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [blocksWithZero], ?_⟩
    intro j hj
    by_contra h
    have hb : 0 ∈ p.block j := by simpa [blocksWithZero, h] using hj
    have hb' := (p.mem_block_iff j 0).mp hb
    omega
  · obtain ⟨j, hj, hij⟩ := p.exists_mem_block hp.m_pos i (by omega)
    have hj0 : j ≠ 0 := by omega
    refine ⟨j, by simpa [blocksWithZero, hj0] using hij, ?_⟩
    intro k hik
    have hk0 : k ≠ 0 := by
      intro hk
      subst k
      simp [blocksWithZero, hi] at hik
    have hk : i ∈ p.block k := by simpa [blocksWithZero, hk0] using hik
    exact p.block_index_unique hp.m_pos hk hij

theorem summable_phases_all : Summable (p.alpha θ) := by
  classical
  apply (summable_partition (fun i => Int.fract_nonneg _) hp.blocksWithZero_partition).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply (summable_nat_add_iff 1).mp
    apply hp.summable_block_phases.congr
    intro n
    simp only [blocksWithZero,
      tsum_fintype, CircleParameterData.alpha]
    exact (Finset.sum_attach (p.block (n + 1)) (fun i => Int.fract ((p.q i : ℝ) * θ))).symm

theorem summable_phases : Summable (fun i : ℕ => p.alpha θ (i + 1)) :=
  (summable_nat_add_iff 1).mpr hp.summable_phases_all

end CircleParameterLaws
end Invariant233

end OAI

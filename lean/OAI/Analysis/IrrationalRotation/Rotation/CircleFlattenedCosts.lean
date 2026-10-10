import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseSummability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

namespace Invariant233.CircleParameterLaws
open scoped BigOperators ENNReal
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem flattenedCost_pos (n : ℕ) : 0 < p.flattenedCost n := by
  exact hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))

theorem tsum_flattened_cost_phase_eq_top :
    (∑' n : ℕ, ENNReal.ofReal (p.flattenedCost n) *
      ENNReal.ofReal (p.alpha θ (n + 1))) = ∞ := by
  classical
  let I := Σ j : ℕ, {i : ℕ // i ∈ p.block (j + 1)}
  let e : I → ℕ := fun a => (a.2 : ℕ) - 1
  have hpos : ∀ j (i : {i : ℕ // i ∈ p.block (j + 1)}), 1 ≤ (i : ℕ) := by
    intro j i
    have h := (p.mem_block_iff (j + 1) i).mp i.property
    omega
  have he : Function.Injective e := by
    rintro ⟨j, i, hi⟩ ⟨k, l, hl⟩ h
    have hip := hpos j ⟨i, hi⟩
    have hlp := hpos k ⟨l, hl⟩
    change 1 ≤ i at hip
    change 1 ≤ l at hlp
    have hil : i = l := by change i - 1 = l - 1 at h; omega
    subst l
    have hjk := p.block_index_unique hp.m_pos hi hl
    have hjk' : j = k := by omega
    subst k
    rfl
  let g : ℕ → ENNReal := fun n => ENNReal.ofReal (p.flattenedCost n) *
    ENNReal.ofReal (p.alpha θ (n + 1))
  have hinner (j : ℕ) :
      (∑' i : {i : ℕ // i ∈ p.block (j + 1)}, g (e ⟨j, i⟩)) =
        ENNReal.ofReal (p.C (j + 1) * ∑ i ∈ p.block (j + 1), p.alpha θ i) := by
    calc
      (∑' i : {i : ℕ // i ∈ p.block (j + 1)}, g (e ⟨j, i⟩)) =
          ∑' i : {i : ℕ // i ∈ p.block (j + 1)},
            ENNReal.ofReal (p.C (j + 1) * p.alpha θ i) := by
        apply tsum_congr
        intro i
        have hi : (i : ℕ) - 1 + 1 = i := by have := hpos j i; omega
        have hc : p.flattenedCost ((i : ℕ) - 1) = p.C (j + 1) :=
          p.flattenedCost_eq_of_mem hp.m_pos (by simpa only [hi] using i.property)
        change ENNReal.ofReal (p.flattenedCost ((i : ℕ) - 1)) *
          ENNReal.ofReal (p.alpha θ ((i : ℕ) - 1 + 1)) = _
        rw [hi, hc, ENNReal.ofReal_mul (hp.C_pos _ (by omega)).le]
      _ = ∑ i ∈ p.block (j + 1), ENNReal.ofReal (p.C (j + 1) * p.alpha θ i) := by
        rw [tsum_fintype]
        exact (Finset.sum_subtype (p.block (j + 1)) (by intro i; rfl)
          (fun i => ENNReal.ofReal (p.C (j + 1) * p.alpha θ i))).symm
      _ = ENNReal.ofReal (p.C (j + 1) * ∑ i ∈ p.block (j + 1), p.alpha θ i) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact mul_nonneg (hp.C_pos _ (by omega)).le (Int.fract_nonneg _)
  have hinf : (∑' a : I, g (e a)) = ∞ := by
    rw [ENNReal.tsum_sigma']
    simp_rw [hinner]
    exact hp.tsum_block_log_cost_eq_top
  have hle := ENNReal.tsum_comp_le_tsum_of_injective he g
  rw [hinf] at hle
  exact top_unique hle

end Invariant233.CircleParameterLaws

end OAI

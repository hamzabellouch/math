import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterConsequences
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Analysis.EndpointIntervalBounds

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem square_m_le_next_K (j : ℕ) (hj : 1 ≤ j) :
    (p.m j : ℝ) ^ 2 ≤ (p.K (j + 1) : ℝ) := by
  have hm : (200 : ℝ) ≤ (p.m j : ℝ) := by exact_mod_cast hp.m_ge_200 j hj
  calc
    (p.m j : ℝ) ^ 2 = (p.m j : ℝ) ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ ≤ (p.m j : ℝ) ^ ((3 / 4 : ℝ) * p.m j) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (p.K (j + 1) : ℝ) := by
      rw [hp.next_K j hj]
      exact Nat.le_ceil _

theorem cutoff_ratio_le_reciprocal_m (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) / p.K (j + 1) ≤ 1 / (p.m j : ℝ) := by
  have hm : 0 < (p.m j : ℝ) := by exact_mod_cast hp.m_pos j hj
  have hKm : (p.K j : ℝ) ≤ (p.m j : ℝ) := by exact_mod_cast hp.m_ge_K j hj
  calc
    (p.K j : ℝ) / p.K (j + 1) ≤ (p.m j : ℝ) / (p.m j : ℝ) ^ 2 :=
      div_le_div₀ hm.le hKm (sq_pos_of_pos hm) (hp.square_m_le_next_K j hj)
    _ = 1 / (p.m j : ℝ) := by field_simp

theorem cutoff_ratio_le_geometric (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) / p.K (j + 1) ≤ (1 / 2 : ℝ) ^ j := by
  have hm : (2 : ℝ) ^ j ≤ (p.m j : ℝ) := by exact_mod_cast hp.m_ge_pow j hj
  calc
    (p.K j : ℝ) / p.K (j + 1) ≤ 1 / (p.m j : ℝ) :=
      hp.cutoff_ratio_le_reciprocal_m j hj
    _ ≤ 1 / (2 : ℝ) ^ j := one_div_le_one_div_of_le (by positivity) hm
    _ = (1 / 2 : ℝ) ^ j := by rw [div_pow, one_pow]

theorem summable_cutoff_ratios :
    Summable (fun n : ℕ => (p.K (n + 1) : ℝ) / p.K (n + 2)) := by
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => hp.cutoff_ratio_le_geometric (n + 1) (by omega))
  exact (summable_nat_add_iff 1).mpr summable_geometric_two

theorem tendsto_cutoff_ratios :
    Tendsto (fun n : ℕ => (p.K (n + 1) : ℝ) / p.K (n + 2)) atTop (𝓝 0) :=
  hp.summable_cutoff_ratios.tendsto_atTop_zero

theorem future_block_budget_le (j : ℕ) (hj : 1 ≤ j) :
    60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤
      120 * (p.K j : ℝ) / p.K (j + 1) := by
  calc
    _ ≤ 60 * (p.K j : ℝ) * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by positivity)
    _ = _ := by ring

theorem future_block_budget_le_geometric (j : ℕ) (hj : 1 ≤ j) :
    60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤
      120 * (1 / 2 : ℝ) ^ j := by
  apply (hp.future_block_budget_le j hj).trans
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (hp.cutoff_ratio_le_geometric j hj) (by norm_num : (0 : ℝ) ≤ 120)

theorem tendsto_future_block_budget :
    Tendsto (fun j : ℕ =>
      60 * (p.K (j + 1) : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 2 + n) : ℝ)))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun j : ℕ => 120 * ((p.K (j + 1) : ℝ) / p.K (j + 2)))
      atTop (𝓝 0) := by
    simpa using hp.tendsto_cutoff_ratios.const_mul 120
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro j
    positivity
  · intro j
    simpa only [mul_div_assoc, show j + 1 + 1 = j + 2 by omega] using
      hp.future_block_budget_le (j + 1) (by omega)

theorem future_endpoint_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (j : ℕ) (hj : 1 ≤ j)
    (X Y : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hdomX : ∀ i, 1 ≤ i → μ.map (X i) ≤ (10 : ℝ≥0∞) • volume.restrict (Set.Ico (0 : ℝ) 1))
    (hdomY : ∀ i, 1 ≤ i → μ.map (Y i) ≤ (10 : ℝ≥0∞) • volume.restrict (Set.Ico (0 : ℝ) 1)) :
    μ.real (⋃ n : ℕ, ⋃ i : p.block (j + 1 + n),
      {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ X i ω ∨
        Y i ω ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)}) ≤
      120 * (p.K j : ℝ) / p.K (j + 1) := by
  classical
  let E : ℕ → Set Ω := fun n => ⋃ i : p.block (j + 1 + n),
    {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ X i ω ∨
      Y i ω ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)}
  have hblock (n : ℕ) : μ.real (E n) ≤
      (60 * (p.K j : ℝ)) * (1 / (p.K (j + 1 + n) : ℝ)) := by
    let s := j + 1 + n
    have hs : 1 ≤ s := by omega
    have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hs).ne'
    have hd : 0 ≤ 3 * (p.K j : ℝ) / p.N s := by
      unfold CircleParameterData.N
      positivity
    calc
      μ.real (E n) ≤ ∑ i : p.block s, μ.real
          {ω | 1 - 3 * (p.K j : ℝ) / p.N s ≤ X i ω ∨
            Y i ω ≤ 3 * (p.K j : ℝ) / p.N s} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : p.block s, 2 * 10 * (3 * (p.K j : ℝ) / p.N s) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : 1 ≤ (i : ℕ) := by
          have hb := (p.mem_block_iff s i).mp i.property
          omega
        exact InvariantRotation.EndpointIntervalBounds.endpoint_pair_loss_le μ
          (hX i) (hY i) (by norm_num) hd (by simpa using hdomX i hi)
          (by simpa using hdomY i hi)
      _ = (60 * (p.K j : ℝ)) * (1 / (p.K s : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          p.card_block s hs, nsmul_eq_mul, CircleParameterData.N]
        field_simp
        ring
  have hs : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have hh := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have h := InvariantRotation.EndpointIntervalBounds.measureReal_iUnion_le_tsum_budget
    μ E (b := fun n => (60 * (p.K j : ℝ)) * (1 / (p.K (j + 1 + n) : ℝ)))
    (fun n => by positivity) (hs.mul_left _) hblock
  have h' : μ.real (⋃ n, E n) ≤
      60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) := by
    simpa only [tsum_mul_left] using h
  exact h'.trans (hp.future_block_budget_le j hj)

end Invariant233.CircleParameterLaws

end

end OAI

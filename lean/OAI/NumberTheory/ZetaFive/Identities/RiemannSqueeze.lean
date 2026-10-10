import Lean.Elab.Tactic.Omega
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.ZetaFive.Identities.WeightedOrder

namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def partitionStep (n : ℕ) (a c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, if x ∈ Set.Ioc (a i) (a (i + 1)) then c i else 0

theorem partitionStep_eq_on_cell {n i : ℕ} {a c : ℕ → ℝ} (ha : Monotone a)
    (hi : i < n) {x : ℝ} (hx : x ∈ Set.Ioc (a i) (a (i + 1))) :
    partitionStep n a c x = c i := by
  classical
  unfold partitionStep
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hx
  · intro j _ hji
    apply ite_eq_right
    intro hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have h := ha (show j + 1 ≤ i by omega)
      exact (not_lt_of_ge (hj.2.trans h)) hx.1
    · have h := ha (show i + 1 ≤ j by omega)
      exact (not_lt_of_ge (hx.2.trans h)) hj.1
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hi))

theorem exists_partition_cell {n : ℕ} {a : ℕ → ℝ} {x : ℝ}
    (hx : x ∈ Set.Ioc (a 0) (a n)) :
    ∃ i < n, x ∈ Set.Ioc (a i) (a (i + 1)) := by
  simpa only [Set.mem_iUnion, Finset.mem_range, exists_prop] using
    Ioc_subset_biUnion_Ioc n a hx

theorem partitionStep_envelopes {n : ℕ} {a l u : ℕ → ℝ} {F : ℝ → ℝ}
    (ha : Monotone a)
    (hcell : ∀ i < n, ∀ x ∈ Set.Ioc (a i) (a (i + 1)), l i ≤ F x ∧ F x ≤ u i) :
    ∀ x ∈ Set.Ioc (a 0) (a n),
      partitionStep n a l x ≤ F x ∧ F x ≤ partitionStep n a u x := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := exists_partition_cell hx
  rw [partitionStep_eq_on_cell ha hi hxi, partitionStep_eq_on_cell ha hi hxi]
  exact hcell i hi x hxi

theorem weightedPrimeIntervalSum_add_adjacent (F : ℝ → ℝ) {α β γ R : ℝ}
    (hαβ : α ≤ β) (hβγ : β ≤ γ) (hR : 0 ≤ R) :
    weightedPrimeIntervalSum F α β R + weightedPrimeIntervalSum F β γ R =
      weightedPrimeIntervalSum F α γ R := by
  unfold weightedPrimeIntervalSum
  simp only [Finset.sum_filter]
  rw [← add_div]
  congr 1
  exact Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then F ((p : ℝ) / R) * Real.log (p : ℝ) else 0)
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hαβ hR))
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hβγ hR))

theorem weightedPrimeIntervalSum_partition (F : ℝ → ℝ) (a : ℕ → ℝ)
    (ha : Monotone a) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∑ i ∈ Finset.range n, weightedPrimeIntervalSum F (a i) (a (i + 1)) R) =
      weightedPrimeIntervalSum F (a 0) (a n) R := by
  induction n with
  | zero => simp [weightedPrimeIntervalSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact weightedPrimeIntervalSum_add_adjacent F (ha (Nat.zero_le n))
      (ha (Nat.le_succ n)) hR

theorem weightedPrimeIntervalSum_partition_bounds
    {n : ℕ} {a l u : ℕ → ℝ} {F : ℝ → ℝ} {R : ℝ}
    (ha : Monotone a) (ha0 : 0 ≤ a 0) (hR : 0 < R)
    (hcell : ∀ i < n, ∀ x ∈ Set.Ioc (a i) (a (i + 1)), l i ≤ F x ∧ F x ≤ u i) :
    finiteStepPrimeSum (Finset.range n) a (fun i => a (i + 1)) l R ≤
        weightedPrimeIntervalSum F (a 0) (a n) R ∧
      weightedPrimeIntervalSum F (a 0) (a n) R ≤
        finiteStepPrimeSum (Finset.range n) a (fun i => a (i + 1)) u R := by
  rw [← weightedPrimeIntervalSum_partition F a ha n hR.le]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact (weightedPrimeIntervalSum_bounds (ha0.trans (ha (Nat.zero_le i)))
      (ha (Nat.le_succ i)) hR (hcell i (Finset.mem_range.mp hi))).1
  · apply Finset.sum_le_sum
    intro i hi
    exact (weightedPrimeIntervalSum_bounds (ha0.trans (ha (Nat.zero_le i)))
      (ha (Nat.le_succ i)) hR (hcell i (Finset.mem_range.mp hi))).2

theorem weightedPrimeIntervalSum_partitionStep
    {n : ℕ} {a c : ℕ → ℝ} {R : ℝ}
    (ha : Monotone a) (ha0 : 0 ≤ a 0) (hR : 0 < R) :
    weightedPrimeIntervalSum (partitionStep n a c) (a 0) (a n) R =
      finiteStepPrimeSum (Finset.range n) a (fun i => a (i + 1)) c R := by
  have h := weightedPrimeIntervalSum_partition_bounds (F := partitionStep n a c) (l := c) (u := c)
    ha ha0 hR (fun i hi x hx => by
      rw [partitionStep_eq_on_cell ha hi hx]
      exact ⟨le_rfl, le_rfl⟩)
  exact le_antisymm h.2 h.1

theorem weightedPrimeIntervalSum_partitionStep_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {n : ℕ} {a c : ℕ → ℝ} (ha : Monotone a) (ha0 : 0 < a 0)
    (hstrict : ∀ i < n, a i < a (i + 1)) :
    Tendsto (weightedPrimeIntervalSum (partitionStep n a c) (a 0) (a n))
      atTop (𝓝 (∑ i ∈ Finset.range n, c i * (a (i + 1) - a i))) := by
  have h := finiteStepPrimeSum_tendsto (Finset.range n) a (fun i => a (i + 1)) c
    hPNT (fun i _ => ha0.trans_le (ha (Nat.zero_le i)))
    (fun i hi => hstrict i (Finset.mem_range.mp hi))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (weightedPrimeIntervalSum_partitionStep ha ha0.le hR).symm

theorem weightedPrimeIntervalSum_tendsto_of_darboux
    {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (_hαβ : α < β)
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    (hDarboux : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (a l u : ℕ → ℝ),
      Monotone a ∧ a 0 = α ∧ a n = β ∧
      (∀ i < n, a i < a (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (a i) (a (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in α..β, F x) - ε < ∑ i ∈ Finset.range n, l i * (a (i + 1) - a i) ∧
      (∑ i ∈ Finset.range n, u i * (a (i + 1) - a i)) < (∫ x in α..β, F x) + ε) :
    Tendsto (weightedPrimeIntervalSum F α β) atTop (𝓝 (∫ x in α..β, F x)) := by
  apply tendsto_order.mpr
  constructor
  · intro v hv
    obtain ⟨n, a, l, u, ha, ha0, han, hs, hb, hl, hu⟩ :=
      hDarboux (((∫ x in α..β, F x) - v) / 2) (by linarith)
    have hp : 0 < a 0 := ha0.symm ▸ hα
    have ht := finiteStepPrimeSum_tendsto (Finset.range n) a (fun i => a (i + 1)) l
      hPNT (fun i _ => hp.trans_le (ha (Nat.zero_le i)))
      (fun i hi => hs i (Finset.mem_range.mp hi))
    have hv' : v < ∑ i ∈ Finset.range n, l i * (a (i + 1) - a i) := by linarith
    filter_upwards [(tendsto_order.mp ht).1 v hv', eventually_gt_atTop (0 : ℝ)] with R hr hR
    have hbound := (weightedPrimeIntervalSum_partition_bounds ha hp.le hR hb).1
    rw [ha0, han] at hbound
    exact hr.trans_le hbound
  · intro v hv
    obtain ⟨n, a, l, u, ha, ha0, han, hs, hb, hl, hu⟩ :=
      hDarboux ((v - (∫ x in α..β, F x)) / 2) (by linarith)
    have hp : 0 < a 0 := ha0.symm ▸ hα
    have ht := finiteStepPrimeSum_tendsto (Finset.range n) a (fun i => a (i + 1)) u
      hPNT (fun i _ => hp.trans_le (ha (Nat.zero_le i)))
      (fun i hi => hs i (Finset.mem_range.mp hi))
    have hv' : (∑ i ∈ Finset.range n, u i * (a (i + 1) - a i)) < v := by linarith
    filter_upwards [(tendsto_order.mp ht).2 v hv', eventually_gt_atTop (0 : ℝ)] with R hr hR
    have hbound := (weightedPrimeIntervalSum_partition_bounds ha hp.le hR hb).2
    rw [ha0, han] at hbound
    exact hbound.trans_lt hr

end Zeta5.Workers.W14

end OAI

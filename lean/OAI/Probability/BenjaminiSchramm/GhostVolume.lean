import OAI.Probability.BenjaminiSchramm.GhostTail
import OAI.Probability.BenjaminiSchramm.EventMeasurability

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_le_truncated_tails (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (N : ℕ) :
    markedConnectionPolynomial G Q x h p ≤
      (h : ℝ) * (∑ i ∈ Finset.range N, finiteClusterTail G Q x (i + 1) p) +
        finiteClusterTail G Q x N p := by
  rw [markedConnection_component_polynomial]
  simp only [finiteClusterTail]
  rw [←bernoulliPolynomial_sum,←bernoulliPolynomial_const_mul,←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  let m := (finiteRootComponent G ω x).card
  change 1 - (1 - (h : ℝ)) ^ m ≤
    (h : ℝ) * (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) +
      if N ≤ m then (1 : ℝ) else 0
  by_cases hm : m ≤ N
  · rw [←natCast_eq_sum_tail m N hm]
    exact (one_sub_pow_one_sub_le h m).trans
      (le_add_of_nonneg_right (by split_ifs <;> norm_num))
  · have hNm : N ≤ m := by omega
    rw [ite_eq_left hNm]
    have hs : 0 ≤ (h : ℝ) *
        (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) :=
      mul_nonneg h.2.1 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    have hp := pow_nonneg (sub_nonneg.mpr h.2.2) m
    linarith

theorem inverse_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℕ) ≤
      2 * (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) := by
  have ha : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hb := Real.sqrt_nonneg (n : ℝ)
  have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have ha2 := Real.sq_sqrt (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity)
  have hb2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  apply (div_le_iff₀ ha).mpr
  have hdiff := sq_nonneg (Real.sqrt (n + 1 : ℕ) - Real.sqrt (n : ℝ))
  norm_num only [Nat.cast_add,Nat.cast_one] at ha2
  norm_num only [Nat.cast_add,Nat.cast_one] at ha hab hdiff ⊢
  nlinarith

theorem sum_inverse_sqrt_le (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / Real.sqrt (i + 1 : ℕ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := inverse_sqrt_step N
    linarith

theorem markedConnection_le_sqrt_scale (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hh : (h : ℝ) * (m : ℝ) ^ 2 ≤ 1)
    (htail : ∀ n : ℕ, 0 < n →
      finiteClusterTail G Q x n p ≤ C / Real.sqrt n) :
    markedConnectionPolynomial G Q x h p ≤ 3 * C / m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmsq : 0 < m ^ 2 := pow_pos hm _
  have hs := Finset.sum_le_sum (s := Finset.range (m ^ 2))
    (fun i _ => htail (i + 1) (by omega))
  have hs' : (∑ i ∈ Finset.range (m ^ 2), finiteClusterTail G Q x (i + 1) p) ≤
      2 * C * m := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m ^ 2), C / Real.sqrt (i + 1 : ℕ) := hs
      _ = C * (∑ i ∈ Finset.range (m ^ 2), 1 / Real.sqrt (i + 1 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ C * (2 * Real.sqrt (m ^ 2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (sum_inverse_sqrt_le (m ^ 2)) hC
      _ = 2 * C * m := by
        rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
        ring
  have ht := htail (m ^ 2) hmsq
  rw [Nat.cast_pow,Real.sqrt_sq (by positivity)] at ht
  have hmark := (markedConnection_le_truncated_tails G Q x p h (m ^ 2)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hs' h.2.1) ht)
  apply hmark.trans
  apply (le_div_iff₀ hmR).mpr
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * C by positivity)
  have hCdiv : (C / (m : ℝ)) * m = C := div_mul_cancel₀ C hmR.ne'
  nlinarith

theorem finiteClusterTail_le_volume_probability [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    finiteClusterTail G Q x n p ≤ (law p (volumeEvent G x n)).toReal := by
  let f (ω : Set E) : ℝ := if n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard then 1 else 0
  have hf : ∀ ω, f ω = f (ω ∩ (Q : Set E)) := by
    intro ω
    simp only [f,Set.inter_assoc,Set.inter_self]
  have he : (∫ ω, f ω ∂law p) = finiteClusterTail G Q x n p := by
    rw [integral_eq_bernoulliPolynomial Q p f hf]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [f,finiteClusterTailIndicator,
      Set.inter_eq_left.mpr (show (ω : Set E) ⊆ Q from hω),
      ←coe_finiteRootComponent,Set.ncard_coe_finset]
  rw [←he]
  change (∫ ω, f ω ∂law p) ≤ (law p).real (volumeEvent G x n)
  rw [←integral_event_indicator p (volumeEvent G x n)
    (measurableSet_volumeEvent G x n)]
  apply integral_mono (integrable_finite_local Q p f hf)
    (by simpa only [Set.indicator,Pi.one_apply] using!
      (integrable_const (1 : ℝ)).indicator (measurableSet_volumeEvent G x n))
  intro ω
  dsimp [f]
  split_ifs with hn hv
  · rfl
  · exfalso
    apply hv
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hn' : (n : ℕ∞) ≤ ((cluster G (ω ∩ (Q : Set E)) x).ncard : ℕ∞) := by
      exact_mod_cast hn
    exact hn'.trans ((Set.ncard_le_encard _).trans
      (Set.encard_le_encard (fun y hy => conn_mono G Set.inter_subset_left hy)))
  · norm_num
  · rfl

theorem finiteClusterTail_le_criticalTail [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ)
    (p : unitInterval) (hp : p ≤ pc G) :
    finiteClusterTail G Q x n p ≤ criticalTail G (volumeEvent G) x n := by
  have hmono := bernoulliPolynomial_monotoneOn Q (finiteClusterTailIndicator G x n)
    (finiteClusterTailIndicator_mono G x n)
  exact (hmono p.2 (pc G).2 hp).trans
    (finiteClusterTail_le_volume_probability G Q x n (pc G))

end Percolation.BenjaminiSchramm

end OAI

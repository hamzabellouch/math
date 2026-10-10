import Mathlib
import OAI.Combinatorics.KMedian.Process.CountInstantiation
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedCount

namespace OAI

section
section
namespace MetricKMedian.SparseFixedCount
open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic FixedBatch
variable {I : Type} [Fintype I] [DecidableEq I]

theorem actual_count_tail (G : I → Finset I) {Δ n : ℕ} {g : ℚ} {p φ b : ℝ}
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*p*(Δ:ℝ) ≤ φ*(g:ℝ))
    (hlarge : 1 < b*amount (fun h => mass (g:ℝ) ((graphActions G).erase h))) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m p φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => 0 < statistic
      (fun e => countOpening D Δ e-mass (g:ℝ) (countErase D Δ e))
      (fun e f => (g:ℝ)*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
      96*(Δ:ℝ)^2*b/(p*φ^2*(g:ℝ)) := by
  dsimp only
  intro enum q hq hqcast
  let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  have hd : 1 ≤ Δ := by
    by_contra hn
    have hz : Δ=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hunit
    linarith
  have hd' : (1:ℝ) ≤ Δ := by exact_mod_cast hd
  have hH : ∀ h ∈ H, 1 < m h := fun h hh =>
    (le_max_left _ _).trans_lt (mem_filter.mp hh).2
  have hB : ∀ h, h ∉ H → m h ≤ b*amount m := by
    intro h hh
    have hn : ¬ max 1 (b*amount m) < m h := fun ht => hh (mem_filter.mpr ⟨mem_univ _,ht⟩)
    exact (le_of_not_gt hn).trans_eq (max_eq_right (show 1 ≤ b*amount m from hlarge.le))
  have hm := graph_mass_sum G hG hunit
  have hmass : (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e)) ≤
      2*amount m/g := by
    rw [masked_mass_sum G H Δ hg hunit hH,nonzero_mass m hm]
    apply (le_div_iff₀ hg).mpr
    simpa only [mul_comm (g:ℝ)] using nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  let D := heavyActions (graphActions G) H
  let ar : HeavyAction (graphActions G) H → ℚ :=
    fun e => if e ∈ D.ordinary ∧ e ∉ balancedActions D Δ then 1 else 0
  let mr : HeavyAction (graphActions G) H → ℚ := fun e => g*(countErase D Δ e).card
  let cr : HeavyAction (graphActions G) H → HeavyAction (graphActions G) H → ℚ :=
    fun e f => g*(overlap (countErase D Δ) e f:ℚ)
  have har : ∀ e, (ar e:ℝ)=countOpening D Δ e := by
    intro e
    simp only [ar,countOpening]
    split_ifs <;> norm_num
  have hmr : ∀ e, (mr e:ℝ)=mass (g:ℝ) (countErase D Δ e) := by
    intro e
    simp only [mr,Rat.cast_mul,Rat.cast_natCast,mass]
  have hcr : ∀ e f, (cr e f:ℝ)=(g:ℝ)*(overlap (countErase D Δ) e f:ℝ) := by
    intro e f
    simp only [cr,Rat.cast_mul,Rat.cast_natCast]
  have h := SparseEnumeratedBernoulli.conditional_count_tail enum q ar mr cr hq hd' hp hφ hg hb hlarge
  simp only [har,hmr,hcr] at h
  apply h
  · intro e
    rw [hqcast]
    exact (bias_upper m hp.le hφ.le _).trans (mul_le_mul_of_nonneg_right (by linarith only [hφ1]) hp.le)
  · intro e
    exact_mod_cast (show (0:ℝ) ≤ ar e by rw [har]; exact countOpening_nonneg _ _ _)
  · intro e
    exact_mod_cast (show (0:ℝ) ≤ mr e by rw [hmr]; exact mass_nonneg hg.le _)
  · exact count_action_size G H hg.le (hg1.trans hlarge.le) hB
  · intro e f; simp only [cr,overlap_symm]
  · intro e; simp only [cr,overlap_self,Nat.cast_zero,mul_zero]
  · intro e f
    dsimp only [cr]
    exact mul_nonneg (by exact_mod_cast hg.le) (Nat.cast_nonneg _)
  · intro e
    apply scaled_overlap_row_bound _ hg.le hd
    intro i
    exact masked_degree _ Δ (fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))) i
  · exact hmass
  · exact masked_total_bound G H hg hunit hG hH
  · exact hsmall
  · simp only [hqcast]
    exact masked_biased_linear_bound G H hg hunit hG hp.le hφ.le hH

end MetricKMedian.SparseFixedCount
end
end

end OAI

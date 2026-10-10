import Mathlib
import OAI.Combinatorics.KMedian.Process.CountGeometry
import OAI.Combinatorics.KMedian.Process.CountSource
import OAI.Combinatorics.KMedian.Process.CountSize
import OAI.Combinatorics.KMedian.Process.CountTail

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_count_tail (G : I → Finset I) {Δ : ℕ} {g p φ b : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : g*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hp1 : (1+φ)*p ≤ 1) (hsmall : 8*p*(Δ:ℝ) ≤ φ*g)
    (hlarge : 1 < b*amount (fun h => mass g ((graphActions G).erase h))) :
    let m := fun h => mass g ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    let q := fun e => bias m p φ (heavyParent (graphActions G) H e)
    let hq0 := fun e => hp.le.trans (bias_lower m hp.le hφ.le _ : p ≤ q e)
    let hq1 := fun e => (bias_upper m hp.le hφ.le _ : q e ≤ (1+φ)*p).trans hp1
    (FiniteLaw.bernoulli q hq0 hq1).prob (fun ω => 0 < statistic
      (fun e => countOpening D Δ e-mass g (countErase D Δ e))
      (fun e f => g*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
      96*(Δ:ℝ)^2*b/(p*φ^2*g) := by
  dsimp only
  let m := fun h => mass g ((graphActions G).erase h)
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
    simpa only [mul_comm g] using nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  apply conditional_count_tail _ _ _ _ _ _ hd' hp hφ hg hb hlarge
  · intro e
    exact (bias_upper m hp.le hφ.le _).trans (mul_le_mul_of_nonneg_right (by linarith only [hφ1]) hp.le)
  · exact countOpening_nonneg _ _
  · intro e; exact mass_nonneg hg.le _
  · exact count_action_size G H hg.le (hg1.trans hlarge.le) hB
  · intro e f; rw [overlap_symm]
  · intro e; rw [overlap_self,Nat.cast_zero,mul_zero]
  · intro e f; positivity
  · intro e
    apply scaled_overlap_row_bound _ hg.le hd
    intro i
    exact masked_degree _ Δ (fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))) i
  · exact hmass
  · exact masked_total_bound G H hg hunit hG hH
  · exact hsmall
  · exact masked_biased_linear_bound G H hg hunit hG hp.le hφ.le hH

end MetricKMedian.FixedBatch
end
end

end OAI

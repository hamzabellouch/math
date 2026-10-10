import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalCountGeometry
import OAI.Combinatorics.KMedian.Process.CountInstantiation

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem unbalanced_small_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g b : ℝ} (hg : 0 < g) (hb : 0 < b) (hunit : g*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ)
    (hsmall : b*amount (fun h => mass g ((graphActions G).erase h)) ≤ 1) :
    let m := fun h => mass g ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    ∀ ω : HeavyAction (graphActions G) H → Bool,
      let D := heavyActions (graphActions G) H
      let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
      mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ 4/(g*b) := by
  dsimp only
  let m := fun h => mass g ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  intro ω
  have hm := graph_mass_sum G hG hunit
  have hH := heavy_card m hg hb (fun h => mass_nonneg hg.le _) hm
    (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hn := nonzero_card m hm (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hnb : ((nonzero m).card:ℝ) ≤ 2/(g*b) := by
    apply (le_div_iff₀ (mul_pos hg hb)).mpr
    have hh := mul_le_mul_of_nonneg_right hn hb.le
    nlinarith only [hh,hsmall]
  let D := heavyActions (graphActions G) H
  let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
  have ho : ((Z ∩ D.ordinary).card:ℝ) ≤ ((nonzero m).card:ℝ) := by
    rw [← masked_openings D Δ ω]
    apply le_trans _ (masked_opening_sum_le G H Δ hg hunit)
    apply sum_le_sum
    intro e _
    have ha := countOpening_nonneg D Δ e
    change countOpening D Δ e * bit ω e ≤ countOpening D Δ e
    unfold bit
    split_ifs
    · simp only [mul_one,le_refl]
    · simpa only [mul_zero] using ha
  have hc := round_count_change A G H Z hg.le hunit
  have he := mass_nonneg hg.le (Z.biUnion D.erase)
  calc
    _ ≤ (H.card:ℝ)+((Z ∩ D.ordinary).card:ℝ) := by linarith only [hc,he]
    _ ≤ 2/(g*b)+2/(g*b) := add_le_add hH (ho.trans hnb)
    _ = 4/(g*b) := by ring

theorem physical_count_tail (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g p φ b : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hp : 0 < p)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : g*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ) (hp1 : (1+φ)*p ≤ 1)
    (hsmall : 8*p*(Δ:ℝ) ≤ φ*g) :
    let m := fun h => mass g ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    let q := fun e => bias m p φ (heavyParent (graphActions G) H e)
    let hq0 := fun e => hp.le.trans (bias_lower m hp.le hφ.le _ : p ≤ q e)
    let hq1 := fun e => (bias_upper m hp.le hφ.le _ : q e ≤ (1+φ)*p).trans hp1
    let hpp1 := (le_mul_of_one_le_left hp.le (by linarith only [hφ] : 1 ≤ 1+φ)).trans hp1
    (PhysicalBatchLaw.law (balancedActions D Δ) (balancedConflicts D Δ) p q hp.le hpp1 hq0 hq1).prob
      (fun Z => mass g A+4/(g*b) < mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
        96*(Δ:ℝ)^2*b/(p*φ^2*g) := by
  classical
  dsimp only
  let m := fun h => mass g ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  let D := heavyActions (graphActions G) H
  let q := fun e => bias m p φ (heavyParent (graphActions G) H e)
  let hq0 := fun e => hp.le.trans (bias_lower m hp.le hφ.le _ : p ≤ q e)
  let hq1 := fun e => (bias_upper m hp.le hφ.le _ : q e ≤ (1+φ)*p).trans hp1
  have hpp1 : p ≤ 1 := (le_mul_of_one_le_left hp.le (by linarith only [hφ])).trans hp1
  let bad := fun Z => mass g A+4/(g*b) < mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))
  have hm := graph_mass_sum G hG hunit
  have hH : (H.card:ℝ) ≤ 2/(g*b) := heavy_card m hg hb (fun h => mass_nonneg hg.le _) hm
    (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hc : 2/(g*b) ≤ 4/(g*b) := div_le_div_of_nonneg_right (by norm_num) (mul_pos hg hb).le
  have hbalance : (FiniteLaw.bernoulli (fun _ : HeavyAction (graphActions G) H => p)
      (fun _ => hp.le) (fun _ => hpp1)).prob
      (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=0 := by
    have he : (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=
        (fun _ => False) := by
      funext ω
      apply propext
      constructor
      · intro hh
        have hbnd := balanced_count_change A G H ω hg.le hunit
        dsimp only [bad] at hh
        linarith only [hbnd,hH,hc,hh]
      · exact False.elim
    simp only [he,FiniteLaw.prob_false]
  have hunbalanced : (FiniteLaw.bernoulli q hq0 hq1).prob
      (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω)) ≤
        96*(Δ:ℝ)^2*b/(p*φ^2*g) := by
    by_cases hlarge : 1 < b*amount m
    · apply le_trans _ (actual_count_tail G hg hg1 hp hφ hφ1 hb hunit hG hp1 hsmall hlarge)
      apply FiniteLaw.prob_mono
      intro ω hh
      have hbnd := unbalanced_count_change A G H ω hg.le hunit
      dsimp only [bad] at hh
      linarith only [hh,hbnd,hH,hc]
    · have he : (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω))=(fun _ => False) := by
        funext ω
        apply propext
        constructor
        · intro hh
          have hbnd := unbalanced_small_change A G hg hb hunit hG (le_of_not_gt hlarge) ω
          dsimp only [bad] at hh
          linarith only [hh,hbnd]
        · exact False.elim
      simp only [he,FiniteLaw.prob_false]
      positivity
  rw [PhysicalBatchLaw.prob_eq]
  change (1/2)*(FiniteLaw.bernoulli _ _ _).prob (fun ω => bad (PhysicalBatchLaw.balanced _ _ ω))+
    (1/2)*(FiniteLaw.bernoulli q hq0 hq1).prob (fun ω => bad (PhysicalBatchLaw.unbalanced _ ω)) ≤ _
  rw [hbalance, mul_zero, zero_add]
  have hnonneg : 0 ≤ 96*(Δ:ℝ)^2*b/(p*φ^2*g) := by positivity
  linarith only [hunbalanced,hnonneg]

end MetricKMedian.CopyState
end
end

end OAI

import OAI.NumberTheory.Jacobsthal.Estimates.UncappedHighRemoval
import OAI.NumberTheory.Jacobsthal.Probability.RetainedCompactEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ActualPrimeHigh

theorem retained_no_high {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hsS : start.ratio ≤ S) (hp : allowed w ell S start ps) :
    ¬actualHasHigh w S start ps := by
  rintro ⟨pre,suf,he,hh⟩
  have hpre := (allowed_append w ell S start pre suf).mp (he ▸ hp) |>.1
  exact (not_lt_of_ge (terminal_ratio_le hsS hpre)) hh

theorem allowed_of_uncapped_prefix_ceiling {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps)
    (hbound : ∀ pre suf : List ℕ, ps = pre++suf → (terminal w start pre).ratio ≤ S) :
    allowed w ell S start ps := by
  classical
  induction ps generalizing start with
  | nil => exact allowed_nil w ell S start
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hpS : (step w start p).ratio ≤ S := by
      simpa only [terminal_cons,terminal_nil] using hbound [p] ps rfl
    have hb : ∀ pre suf : List ℕ, ps = pre++suf →
        (terminal w (step w start p) pre).ratio ≤ S := by
      intro pre suf he
      exact hbound (p::pre) suf (by rw [List.cons_append,he])
    obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell S start p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hpS⟩,ih ht hb⟩

theorem allowed_iff_uncapped_no_high {w ell S : ℝ} {start : Node} (hsS : start.ratio ≤ S)
    (ps : List ℕ) : allowed w ell S start ps ↔
      uncappedAllowed w ell start ps ∧ ¬actualHasHigh w S start ps := by
  constructor
  · intro hp
    exact ⟨(uncapped_iff_exists_ceiling w ell start ps).mpr ⟨S,hsS,hp⟩,retained_no_high hsS hp⟩
  · rintro ⟨hp,hh⟩
    apply allowed_of_uncapped_prefix_ceiling hp
    intro pre suf he
    exact le_of_not_gt (fun h => hh ⟨pre,suf,he,h⟩)

theorem retained_eq_nonhigh {w ell S : ℝ} (hw : 1 < w) {start : Node} (hsS : start.ratio ≤ S) :
    retainedPrefixes w ell S start =
      (uncappedPrefixes w ell start).filter (fun ps => ¬actualHasHigh w S start ps) := by
  classical
  ext ps
  rw [mem_retainedPrefixes hw,Finset.mem_filter,mem_uncappedPrefixes hw]
  exact allowed_iff_uncapped_no_high hsS ps

theorem uncapped_sum_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (F : List ℕ → ℝ) :
    (∑ ps ∈ uncappedPrefixes w ell start,F ps) =
      (∑ ps ∈ retainedPrefixes w ell S start,F ps) +
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),F ps := by
  classical
  rw [retained_eq_nonhigh hw hsS]
  exact (Finset.sum_filter_not_add_sum_filter _ _ _).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.CompactSelectedPartition

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeFamilyOccupation ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem selected_uncapped_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (E : Set (List ℕ)) :
    (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) =
      (∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps) +
      ∑ ps ∈ ((uncappedPrefixes w ell start).filter (actualHasHigh w S start)).filter (· ∈ E),
        prefixWeight ps := by
  have h := uncapped_sum_partition (ell:=ell) hw hsS (fun ps => if ps ∈ E then prefixWeight ps else 0)
  simpa only [Finset.sum_filter] using h

theorem selected_uncapped_le {w ell S R : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (E : Set (List ℕ))
    (hcompact : ∀ ps ∈ uncappedPrefixes w ell start,ps ∈ E → (terminal w start ps).gap ≤ R) :
    (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps) +
      uncappedLowGapHighMass w ell start S R := by
  rw [selected_uncapped_partition hw hsS E]
  apply add_le_add le_rfl
  unfold uncappedLowGapHighMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hhigh,hE⟩ := Finset.mem_filter.mp hp
    obtain ⟨hps,hh⟩ := Finset.mem_filter.mp hhigh
    exact Finset.mem_filter.mpr ⟨hps,hcompact ps hps hE,hh⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

end NumberTheoryLean.CompactSelectedPartition

end

end Erdos970

end OAI

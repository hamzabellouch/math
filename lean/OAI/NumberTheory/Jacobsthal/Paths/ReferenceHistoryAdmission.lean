import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceLocalResidual
import OAI.NumberTheory.Jacobsthal.Primes.PrimeCompactWeights

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHistoryAdmission

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence ReferenceSourcePrimeSets ReferenceEulerRecurrence
open ReferenceCancellation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem cap_lower_ratio {w : ℝ} {z : Node} {p : ℕ} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hx : 0 < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p)) :
    z.ratio-1 ≤ childRatio w z.gap p := by
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact h.le
    | true => simpa [capGuard,hcl] using hcap
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hm := mul_le_mul_of_nonneg_right hxp (valid_pos hs).le
  have hd : z.ratio ≤ z.gap/primeExponent w p := (le_div_iff₀ hx).mpr (by nlinarith)
  unfold childRatio
  linarith

theorem uncapped_child_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hz : Consistent z) (p : ℕ) :
    p ∈ uncappedChildren w 2 z ↔ p ∈ highPrimes w z.cutoff z.closed ∧
      childAdmitted z.side z.gap (primeExponent w p) := by
  constructor
  · intro hp
    obtain ⟨hprime,hx,hcap,hmin⟩ := Finset.mem_filter.mp hp
    have hpP := (Nat.mem_primesLE.mp hprime).2
    refine ⟨(highPrimes_membership hw z.cutoff z.closed p).mpr ⟨hpP,hx,hcap⟩,?_⟩
    cases hi : z.side with
    | even => trivial
    | odd =>
      rw [hi] at hmin
      apply (upper_admission_above_two hx.le).mpr
      have h2 : 2 ≤ childRatio w z.gap p := (le_max_left _ _).trans hmin
      have hdiv : 3 ≤ z.gap/primeExponent w p := by unfold childRatio at h2; linarith
      have hm := (le_div_iff₀ (by linarith : 0 < primeExponent w p)).mp hdiv
      linarith
  · rintro ⟨hp,ha⟩
    obtain ⟨hpP,hx,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hp
    have hx0 : 0 < primeExponent w p := by linarith
    have hxp : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hpLe := (exponent_le_iff hw (by exact_mod_cast hpP.pos)).mp hxp
    have hprime := Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) z.cutoff).le).mpr hpLe,hpP⟩
    apply Finset.mem_filter.mpr
    refine ⟨hprime,hx,hcap,?_⟩
    have hlo := cap_lower_ratio hs hz hx0 hcap
    cases hi : z.side with
    | even => exact hlo
    | odd =>
      rw [hi] at ha
      apply max_le
      · have hh := (upper_admission_above_two hx.le).mp ha
        unfold childRatio
        have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ hx0).mpr (by linarith)
        linarith
      · exact hlo

theorem uncapped_child_invariants {w : ℝ} {z : Node} {p : ℕ}
    (hs : Valid z.side z.ratio) (hr : 0 < z.gap) (hp : p ∈ uncappedChildren w 2 z) :
    Valid (step w z p).side (step w z p).ratio ∧ 0 < (step w z p).gap ∧ Consistent (step w z p) := by
  have hone : uncappedAllowed w 2 z [p] := ⟨hp,trivial⟩
  obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w 2 z [p]).mp hone
  have hc := ((allowed_cons w 2 U z p []).mp hU).1
  exact ⟨child_valid hs hc,child_gap_positive (by norm_num) hr hs hc,step_consistent (by norm_num) hr hs hc⟩

theorem decreasing_cons_iff (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ decreasingPrefixes P ↔ p ∈ P ∧ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)) := by
  constructor
  · intro h
    have hp := (mem_decreasingPrefixes.mp h).2 p (by simp)
    refine ⟨hp,?_⟩
    have ht := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp h
    simpa [suffixPrimes] using ht
  · rintro ⟨hp,ht⟩
    apply (append_mem_decreasing_iff (singleton_prefix_mem hp)).mpr
    simpa [suffixPrimes] using ht

theorem referencePrefixes_cons_iff (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w P i r ↔ p ∈ P ∧ childAdmitted i r (primeExponent w p) ∧
      ps ∈ referencePrefixes w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) := by
  simp only [referencePrefixes,Finset.mem_filter,decreasing_cons_iff,admitted]
  tauto

theorem reference_history_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (ps : List ℕ) :
    ps ∈ referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap ↔ uncappedAllowed w 2 z ps := by
  induction ps generalizing z with
  | nil => simp [referencePrefixes,mem_decreasingPrefixes,admitted,uncappedAllowed]
  | cons p ps ih =>
    rw [referencePrefixes_cons_iff]
    constructor
    · rintro ⟨hp,ha,ht⟩
      have hpU := (uncapped_child_iff hw hs hz p).mpr ⟨hp,ha⟩
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      rw [← he] at ht
      exact ⟨hpU,(ih hvs hrs hzs).mp ht⟩
    · rintro ⟨hpU,htU⟩
      obtain ⟨hp,ha⟩ := (uncapped_child_iff hw hs hz p).mp hpU
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have ht := (ih hvs hrs hzs).mpr htU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      change ps ∈ referencePrefixes w (highPrimes w (primeExponent w p) false) z.side.flip (z.gap-primeExponent w p) at ht
      rw [he] at ht
      exact ⟨hp,ha,ht⟩

theorem reference_family_eq_uncapped {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) :
    referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap=uncappedPrefixes w 2 z := by
  ext ps
  rw [reference_history_iff hw hs hr hz,mem_uncappedPrefixes hw]

end NumberTheoryLean.ReferenceHistoryAdmission

end

end Erdos970

end OAI

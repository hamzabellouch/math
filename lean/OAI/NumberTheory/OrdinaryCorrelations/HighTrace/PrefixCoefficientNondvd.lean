import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExistsNewPrime
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LastEdge
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ReverseSegment

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

theorem prefix_coefficient_nondvd (s : S.Specification D h L) (hs : s.Primitive)
    (q r : S.Index) (hrt : (r:ℕ) ∣ s.label s.tailStart)
    (hrfree : ∀ i : Fin s.length, i<s.tailStart → ¬(r:ℕ) ∣ s.label i)
    (hq : ∃ i : Fin s.length, i<s.tailStart ∧ (q:ℕ) ∣ s.label i) :
    ¬((r:ℕ):ℤ) ∣ s.coefficient q 0 s.tailStart.val := by
  let A := univ.filter (fun i : Fin s.length => i<s.tailStart ∧ (q:ℕ) ∣ s.label i)
  have hA : A.Nonempty := by
    obtain ⟨i,hi,hqi⟩ := hq
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi,hqi⟩⟩
  let a := A.min' hA
  let b := A.max' hA
  have ha := (mem_filter.mp (min'_mem A hA)).2
  have hb := (mem_filter.mp (max'_mem A hA)).2
  have hab : a ≤ b := min'_le A b (max'_mem A hA)
  have hbl : b.val+1 ≤ s.tailStart.val := by
    have htt : b<s.tailStart := hb.1
    change b.val<s.tailStart.val at htt
    omega
  have hinterval (i : Fin s.length) (hai : a.val ≤ i.val) (hib : i.val<b.val+1) :
      (q:ℕ) ∣ s.label i :=
    s.prime_occurrence_interval hs q a i b hai (by change i.val ≤ b.val; omega) ha.2 hb.2
  have hrestrict : s.coefficient q 0 s.tailStart.val = s.coefficient q a.val (b.val+1) := by
    apply s.coefficient_restrict q a.val (b.val+1) 0 s.tailStart.val
      (Nat.zero_le _) hbl s.tailStart.isLt.le
    intro i hzero hit hout hqi
    have hi : i ∈ A := mem_filter.mpr ⟨mem_univ _,hit,hqi⟩
    rcases hout with hil|hir
    · have hm : a ≤ i := min'_le A i hi
      change a.val ≤ i.val at hm
      omega
    · have hm : i ≤ b := le_max' A i hi
      change i.val ≤ b.val at hm
      omega
  have hmul := s.mul_coefficient_interval q a.val (b.val+1)
    (by have hh : a.val ≤ b.val := hab; omega) (by omega) hinterval
  intro hd
  rw [hrestrict] at hd
  have hdiv : ((r:ℕ):ℤ) ∣ s.offset ⟨b.val+1,by omega⟩-s.offset ⟨a.val,by omega⟩ := by
    rw [← hmul]
    exact dvd_mul_of_dvd_right hd _
  exact s.primitive_prefix_nondvd hs r s.tailStart hrt hrfree a.val (b.val+1)
    (by have hh : a.val ≤ b.val := hab; omega) hbl hdiv

theorem primitive_coefficient_inputs (s : S.Specification D h L) (hs : s.Primitive)
    (hh : 0<h) (hτ : τ<2) (hpp : h<(s.extra:ℕ)) (hpL : L<(s.extra:ℕ)) :
    ∃ r : S.Index,
      (r:ℕ) ∣ s.label s.tailStart ∧
      (∀ i : Fin s.length, i<s.tailStart → ¬(r:ℕ) ∣ s.label i) ∧
      (∀ q : S.Index, (q:ℕ) ∣ s.label s.tailStart →
        (∀ i : Fin s.length, i<s.tailStart → ¬(q:ℕ) ∣ s.label i) →
        ¬((s.extra:ℕ):ℤ) ∣ s.coefficient q s.suffix.val s.length) ∧
      (∀ q : S.Index, (∃ i : Fin s.length, i<s.tailStart ∧ (q:ℕ) ∣ s.label i) →
        ¬((r:ℕ):ℤ) ∣ s.coefficient q 0 s.tailStart.val) := by
  obtain ⟨r,hrt,hrfree⟩ := s.exists_tail_prime hs hh hτ hpp hpL
  exact ⟨r,hrt,hrfree,
    fun q hq hfree => s.suffix_coefficient_nondvd hh hpp hpL q hq hfree,
    fun q hq => s.prefix_coefficient_nondvd hs q r hrt hrfree hq⟩

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI

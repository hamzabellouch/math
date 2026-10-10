import OAI.NumberTheory.Jacobsthal.Paths.MovingStopMargins
import OAI.NumberTheory.Jacobsthal.Paths.StoppedReferenceFinite

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosStoppedReferenceUpper
open NumberTheoryLean FinitePathGeometry PrimeHistories ReferencePruning ReferenceAdmission
open ReferenceProductsBasics ReferenceSourcePrimeSets LogarithmicBinPartition
open StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open ErdosPrimeInputs.PrimePrefixMass

theorem below_all_iff_last (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·)) (q : ℕ) :
    (∀ p ∈ ps,q<p) ↔ q<ps.getLastD 0 := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  constructor
  · intro h
    exact h _ (List.getLast_mem hne)
  · intro h p hp
    have hdec' : (ps.dropLast++[ps.getLast hne]).Pairwise (· > ·) := by
      rwa [List.dropLast_append_getLast]
    rw [← List.dropLast_append_getLast hne] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.trans ((List.pairwise_append.mp hdec').2.2 p hp _ (by simp))
    · have heq := List.mem_singleton.mp hp
      simpa only [heq] using h

theorem suffix_source_primes {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·))
    (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    suffixPrimes (sourcePrimeSet w top) ps=availablePrimes w (ps.getLastD 0:ℝ) false := by
  classical
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hlastP := (mem_sourcePrimeSet hw htop _).mp (hsource _ hlast)
  have hp0 : 0 ≤ (ps.getLastD 0:ℝ) := Nat.cast_nonneg _
  ext q
  rw [suffixPrimes,Finset.mem_filter,mem_sourcePrimeSet hw htop,
    availablePrimes_membership hp0]
  simp only [Bool.false_eq_true,ite_false]
  rw [below_all_iff_last ps hne hdec q]
  constructor
  · rintro ⟨⟨hq,hwq,_⟩,hql⟩
    exact ⟨hq,hwq,by exact_mod_cast hql⟩
  · rintro ⟨hq,hwq,hql⟩
    exact ⟨⟨hq,hwq,hql.le.trans hlastP.2.2⟩,by exact_mod_cast hql⟩

theorem after_source_primes {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (v : Vertex) (hv : v.available=sourcePrimeSet w top)
    (ps : List ℕ) (hne : ps ≠ []) (hdec : ps.Pairwise (· > ·))
    (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    (after w v ps).available=availablePrimes w (ps.getLastD 0:ℝ) false := by
  rw [after_available,hv]
  exact suffix_source_primes hw htop ps hne hdec hsource

theorem after_original_scale (w : ℝ) (Y : ℕ) (z : Node) (P : Finset ℕ) (ps : List ℕ) :
    (after w (rootVertex z ∅ P ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) ps).scale=
      ((Y:ℝ)/(ps.prod:ℝ))*ErdosPrimeInputs.MertensStrong.primeProduct w := by
  rw [after_scale_product]
  change ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)/(ps.prod:ℝ)=_
  ring

theorem actual_stopped_vertex_data {n : ℕ} (Y : ℕ)
    (w top Cs eta Clen B xi b₀ b₁ : ℝ) (hw : 0 < w) (htop : w < top)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (ps : List ℕ)
    (hp : ps ∈ stopped w (SourceStopPredicate.stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (sourcePrimeSet w top).card
      (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w))) :
    (terminal w z ps).side=.even ∧ ps ≠ [] ∧ ps.Pairwise (· > ·) ∧
      (after w (rootVertex z ∅ (sourcePrimeSet w top)
        ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) ps).available=
        availablePrimes w (ps.getLastD 0:ℝ) false := by
  classical
  have hf := ActualSourceStopBinding.actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁
    ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w) lower width label a z (sourcePrimeSet w top) hp
  have ht := StoppedTraceAdmission.trace_reference_member w
    (SourceStopPredicate.stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
    (sourcePrimeSet w top).card
    (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*ErdosPrimeInputs.MertensStrong.primeProduct w)) (Or.inr hp)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp ht).1
  refine ⟨hf.1,hf.2.1.1,hd.1,?_⟩
  exact after_source_primes hw htop _ rfl ps hf.2.1.1 hd.1 hd.2

end ErdosStoppedReferenceUpper

end

end Erdos970

end OAI

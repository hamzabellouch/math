import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationUnitsPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationAncestors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open scoped BigOperators
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryFrequencyResidues
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma rootSlot_coprime_outside (h : History l) (hs : h.Supported V outside)
    (q : SmallSlot) (hq : q∈h.root.small) : Nat.Coprime q.value outside.prod := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  apply (List.pairwise_append.mp (History.supported_root_coprime hs)).2.2 q.value _ p hp
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))

theorem internalSlot_coprime_outside (h : History l) (hs : h.Supported V outside)
    (i : InternalKey h) : Nat.Coprime (internalSlot h i).value outside.prod := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · exact rootSlot_coprime_outside left (History.supported_left hs) _
        ((History.supported_child_small hs).1.mem_iff.mpr (List.mem_append_left _ (List.get_mem _ i)))
    · exact ihl (History.supported_left hs) i
    · exact ihr (History.supported_right hs) i

theorem representative_coprime_outside (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside) (r : Representative h g) :
    Nat.Coprime (prime h g r) outside.prod := by
  obtain ⟨i,rfl⟩ := label_surjective h g r
  rcases i with i | i
  · exact internalSlot_coprime_outside h hs i
  · exact internalSlot_coprime_outside g gs i

theorem representative_coprime_frequency (sources : SourceFamily) (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass sources (internalSlot g i)≠0)
    (hf : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j))
    (r : Representative h g) (n : ℕ) :
    Nat.Coprime (prime h g r) (FrequencyPrecision.product (h.frequencies++g.frequencies)^n) := by
  obtain ⟨i,rfl⟩ := label_surjective h g r
  rcases i with i | i
  · exact sourceMass_coprime_paired_frequency h g hs gs hf _ (hm i) n
  · exact sourceMass_coprime_paired_frequency h g hs gs hf _ (gm i) n

theorem representative_coprime_root (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0)
    (hr : ∀q∈h.root.small,sourceMass C.sources q≠0)
    (r : Representative h g) : Nat.Coprime (prime h g r) (h.root.small.map SmallSlot.value).prod := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨j,rfl⟩ := List.get_of_mem hq
  obtain ⟨i,rfl⟩ := label_surjective h g r
  have hprime : h.root.PrimeSmall := by rw [History.Supported.eq_def] at hs; exact hs.2.1
  rcases i with i | i
  · exact (Nat.coprime_primes (internalSlot_prime h hs i) (hprime _ (List.get_mem _ j))).mpr
      (internalSlot_ne_rootSlot C hsep h h hh hh hs hs hm hr i j)
  · exact (Nat.coprime_primes (internalSlot_prime g gs i) (hprime _ (List.get_mem _ j))).mpr
      (internalSlot_ne_rootSlot C hsep g h gh hh gs hs gm hr i j)

theorem actual_crt_coprimality (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0)
    (hr : ∀q∈h.root.small,sourceMass C.sources q≠0)
    (hf : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hout : ∀p∈outside,p.Prime ∧ ∀j ≤ l,V j<p) (n : ℕ) :
    let A := (h.root.small.map SmallSlot.value).prod
    let D := outside.prod
    let Q := FrequencyPrecision.product (h.frequencies++g.frequencies)^n
    let B := ∏r : Representative h g,(prime h g r)^2
    Nat.Coprime A D ∧ Nat.Coprime A Q ∧ Nat.Coprime A B ∧
      Nat.Coprime D Q ∧ Nat.Coprime D B ∧ Nat.Coprime Q B := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply Nat.coprime_list_prod_left_iff.mpr
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact rootSlot_coprime_outside h hs q hq
  · exact source_slots_product_coprime C.sources _
      (fun q hq=>sourceMass_coprime_paired_frequency h g hs gs hf q hq n) _ hr
  · apply Nat.coprime_prod_right_iff.mpr
    intro r _
    exact (representative_coprime_root C hsep h g hh gh hs gs hm gm hr r).symm.pow_right 2
  · apply Nat.coprime_list_prod_left_iff.mpr
    intro p hp
    exact small_coprime_frequency_power h g hs gs p (hout p hp).1 (hout p hp).2 n
  · apply Nat.coprime_prod_right_iff.mpr
    intro r _
    exact (representative_coprime_outside h g hs gs r).symm.pow_right 2
  · apply Nat.coprime_prod_right_iff.mpr
    intro r _
    exact (representative_coprime_frequency C.sources h g hs gs hm gm hf r n).symm.pow_right 2

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI

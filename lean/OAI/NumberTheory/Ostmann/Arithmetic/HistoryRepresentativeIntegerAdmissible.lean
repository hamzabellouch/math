import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible
open scoped BigOperators
open Filter Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryPairPattern
open HistoryRepresentativeSourceSeparation HistoryGiantReferenceMean HistorySignedXiTransport
open HistoryGiantXiReplacementActual

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem decoded_integer_pair_admissible (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
    (x y : SourceAssignment C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (s t P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (hx : (assignmentPrior C.sources _).mass x≠0)
    (hy : (assignmentPrior C.sources _).mass y≠0)
    (hc : choicesMass C.sources _ V l c≠0) (he : choicesMass C.sources _ V l e≠0)
    (hf : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hout : ∀p∈outside,p.Prime ∧ ∀j ≤ l,V j<p)
    (hs : (decodeHistory C.sources _ V l (giantState (sourceState C.sources _ x s) P Q) c).Supported V outside)
    (gs : (decodeHistory C.sources _ V l (giantState (sourceState C.sources _ y t) P Q) e).Supported V outside) :
    PairAdmissible (decodeHistory C.sources _ V l (giantState (sourceState C.sources _ x s) P Q) c)
      (decodeHistory C.sources _ V l (giantState (sourceState C.sources _ y t) P Q) e) outside := by
  let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
  let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources _ x s) P Q) c
  let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources _ y t) P Q) e
  have hh : TreeSourceLabels seed h := assigned_giant_tree_source_labels C.sources seed V l x s P Q c
  have gh : TreeSourceLabels seed g := assigned_giant_tree_source_labels C.sources seed V l y t P Q e
  have hm := decoded_internalSlot_mass C.sources seed V l (giantState (sourceState C.sources _ x s) P Q) c hc
  have gm := decoded_internalSlot_mass C.sources seed V l (giantState (sourceState C.sources _ y t) P Q) e he
  have hr : ∀q∈h.root.small,sourceMass C.sources q≠0 := by
    simpa only [h,decodeHistory_root,giantState,sourceState] using assignedSlots_source_mass_ne_zero
      C.sources _ x hx
  have gr : ∀q∈g.root.small,sourceMass C.sources q≠0 := by
    simpa only [g,decodeHistory_root,giantState,sourceState] using assignedSlots_source_mass_ne_zero
      C.sources _ y hy
  exact ⟨representative_prime_injective C hsep h g hh gh hs gs hm gm,
    representative_squares_pairwise C hsep h g hh gh hs gs hm gm,
    actual_ancestor_units C hsep h g hh gh hs gs hm gm hr gr,
    fun n=>actual_crt_coprimality C hsep h g hh gh hs gs hm gm hr hf hout n⟩

theorem selected_integer_pair_admissible_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
        (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
          Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ outside : List ℕ,(∀p∈outside,p∈spectator.candidates) →
      ∀l,l≤k →
      ∀(x y : SourceAssignment C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
        (s t P Q : ℤ)
        (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k)
          (Conclusion.frequencyBound Bs BD Bz k L) l),
        (assignmentPrior C.sources _).mass x≠0 → (assignmentPrior C.sources _).mass y≠0 →
        choicesMass C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l c≠0 →
        choicesMass C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l e≠0 →
        (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
          (giantState (sourceState C.sources _ x s) P Q) c).Supported (Conclusion.frequencyBound Bs BD Bz k L) outside →
        (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
          (giantState (sourceState C.sources _ y t) P Q) e).Supported (Conclusion.frequencyBound Bs BD Bz k L) outside →
        PairAdmissible
          (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
            (giantState (sourceState C.sources _ x s) P Q) c)
          (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
            (giantState (sourceState C.sources _ y t) P Q) e) outside := by
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hk,
    initial_sources_above_frequencies_eventually d Bs BD Bz hk,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/2000)] with L hsep hfreq hspecfreq
  intro E C hG hc hcu hb hd spectator hspec outside hout l hl x y s t P Q c e hx hy hc' he hs gs
  apply decoded_integer_pair_admissible C (hsep E C hG hc hcu hb hd spectator hspec)
    _ outside l x y s t P Q c e hx hy hc' he _ _ hs gs
  · exact fun j hj=>(hfreq E C hG hc hcu hb hd j (hj.trans hl)).2
  · intro p hp
    refine ⟨spectator.prime p (hout p hp),?_⟩
    intro j hj
    exact hspecfreq j (hj.trans hl) p (spectator.prime p (hout p hp)).pos
      (hspec ⟨p,hout p hp⟩).1

end Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible

end

end OAI

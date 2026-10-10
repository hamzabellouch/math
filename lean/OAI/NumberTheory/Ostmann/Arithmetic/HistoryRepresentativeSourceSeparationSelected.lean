import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationModuli
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open scoped BigOperators
open Filter Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryPairPattern

def CRTCompatible {l : ℕ} (h g : History l) (outside : List ℕ) (n : ℕ) : Prop :=
  let A := (h.root.small.map SmallSlot.value).prod
  let D := outside.prod
  let Q := FrequencyPrecision.product (h.frequencies++g.frequencies)^n
  let B := ∏r : Representative h g,(prime h g r)^2
  Nat.Coprime A D ∧ Nat.Coprime A Q ∧ Nat.Coprime A B ∧
    Nat.Coprime D Q ∧ Nat.Coprime D B ∧ Nat.Coprime Q B

def PairAdmissible {l : ℕ} (h g : History l) (outside : List ℕ) : Prop :=
  Function.Injective (prime h g) ∧
    Pairwise (fun a b : Representative h g=>Nat.Coprime ((prime h g a)^2) ((prime h g b)^2)) ∧
    (∀i : Occurrences h g, AncestorUnits h g
      (fun j=>(pairSample h g j:ZMod (slot h g i).value)) i) ∧
    ∀n,CRTCompatible h g outside n

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem decoded_outer_pair_admissible (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
    (x y : OuterSample C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant)
    (s t : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (hx : (outerPrior C.sources _ C.giant).mass x≠0)
    (hy : (outerPrior C.sources _ C.giant).mass y≠0)
    (hc : choicesMass C.sources _ V l c≠0) (he : choicesMass C.sources _ V l e≠0)
    (hf : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hout : ∀p∈outside,p.Prime ∧ ∀j ≤ l,V j<p)
    (hs : (decodeHistory C.sources _ V l (outerState C.sources _ C.giant x s) c).Supported V outside)
    (gs : (decodeHistory C.sources _ V l (outerState C.sources _ C.giant y t) e).Supported V outside) :
    PairAdmissible (decodeHistory C.sources _ V l (outerState C.sources _ C.giant x s) c)
      (decodeHistory C.sources _ V l (outerState C.sources _ C.giant y t) e) outside := by
  let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
  let h := decodeHistory C.sources seed V l (outerState C.sources _ C.giant x s) c
  let g := decodeHistory C.sources seed V l (outerState C.sources _ C.giant y t) e
  have hh : TreeSourceLabels seed h := decoded_tree_source_labels _ _ _ _ _ _
    (Template.assignedSlots_matches _ _ _)
  have gh : TreeSourceLabels seed g := decoded_tree_source_labels _ _ _ _ _ _
    (Template.assignedSlots_matches _ _ _)
  have hm := decoded_internalSlot_mass C.sources seed V l (outerState C.sources _ C.giant x s) c hc
  have gm := decoded_internalSlot_mass C.sources seed V l (outerState C.sources _ C.giant y t) e he
  have hx' : C.giant.law.mass x.1*(C.giant.law.mass x.2.1*
      (assignmentPrior C.sources (Template.current seed l)).mass x.2.2)≠0 := hx
  have hy' : C.giant.law.mass y.1*(C.giant.law.mass y.2.1*
      (assignmentPrior C.sources (Template.current seed l)).mass y.2.2)≠0 := hy
  have hr : ∀q∈h.root.small,sourceMass C.sources q≠0 := by
    simpa only [h,decodeHistory_root,outerState] using assignedSlots_source_mass_ne_zero
      C.sources _ x.2.2 (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  have gr : ∀q∈g.root.small,sourceMass C.sources q≠0 := by
    simpa only [g,decodeHistory_root,outerState] using assignedSlots_source_mass_ne_zero
      C.sources _ y.2.2 (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy').2).2
  exact ⟨representative_prime_injective C hsep h g hh gh hs gs hm gm,
    representative_squares_pairwise C hsep h g hh gh hs gs hm gm,
    actual_ancestor_units C hsep h g hh gh hs gs hm gm hr gr,
    fun n=>actual_crt_coprimality C hsep h g hh gh hs gs hm gm hr hf hout n⟩

theorem selected_pair_admissible_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      ∀(x y : OuterSample C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant)
        (s t : ℤ)
        (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k)
          (Conclusion.frequencyBound Bs BD Bz k L) l),
        (outerPrior C.sources _ C.giant).mass x≠0 → (outerPrior C.sources _ C.giant).mass y≠0 →
        choicesMass C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l c≠0 →
        choicesMass C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l e≠0 →
        (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
          (outerState C.sources _ C.giant x s) c).Supported (Conclusion.frequencyBound Bs BD Bz k L) outside →
        (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
          (outerState C.sources _ C.giant y t) e).Supported (Conclusion.frequencyBound Bs BD Bz k L) outside →
        PairAdmissible
          (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
            (outerState C.sources _ C.giant x s) c)
          (decodeHistory C.sources _ (Conclusion.frequencyBound Bs BD Bz k L) l
            (outerState C.sources _ C.giant y t) e) outside := by
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hk,
    initial_sources_above_frequencies_eventually d Bs BD Bz hk,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/2000)] with L hsep hfreq hspecfreq
  intro E C hG hc hcu hb hd spectator hspec outside hout l hl x y s t c e hx hy hc' he hs gs
  apply decoded_outer_pair_admissible C (hsep E C hG hc hcu hb hd spectator hspec)
    _ outside l x y s t c e hx hy hc' he _ _ hs gs
  · exact fun j hj=>(hfreq E C hG hc hcu hb hd j (hj.trans hl)).2
  · intro p hp
    refine ⟨spectator.prime p (hout p hp),?_⟩
    intro j hj
    exact hspecfreq j (hj.trans hl) p (spectator.prime p (hout p hp)).pos
      (hspec ⟨p,hout p hp⟩).1

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI

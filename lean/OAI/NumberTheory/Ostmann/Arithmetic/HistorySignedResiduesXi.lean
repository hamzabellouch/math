import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionResidue
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedXiTransport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction HistorySignedXiTransport
open HistorySymbolicEncoding

theorem changed_supported_iff (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) (Xp Xm : ℤ)
    (hlarge : HistorySupportReduction.LargePrimes V
      (decodeHistory sources seed V l (giantState a Xp Xm) c)) :
    (decodeHistory sources seed V l (giantState a Xp Xm) c).Supported V outside ↔
      (rebuild (decodeHistory sources seed V l a c) Xp Xm).PositiveIntegral ∧
      Nat.Coprime Xp.natAbs Xm.natAbs ∧
      ResidueGuarded V outside (rebuild (decodeHistory sources seed V l a c) Xp Xm) := by
  simpa only [rebuild_decodeHistory, giantState, SignedState.toState] using
    supported_iff_positiveIntegral_residue sources seed V l
      ⟨a.frequency,Xp,Xm,a.small⟩ c outside ha hlarge

lemma supportedHistoryPairXi_eq_zero_of_not {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hn : ¬(h.Supported V outside ∧ k.Supported V outside)) :
    supportedHistoryPairXi d V outside b s X tb td G h k = 0 := by
  classical
  by_cases hs : h.Supported V outside
  · have hk : ¬k.Supported V outside := fun hk => hn ⟨hs,hk⟩
    simp only [supportedHistoryPairXi,dite_eq_left hs,dite_eq_right hk]
  · simp only [supportedHistoryPairXi,dite_eq_right hs]

theorem supportedHistoryPairXi_eq_residueTest (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (Xp Xm : ℤ) (hp : 0 < Xp) (hm : 0 < Xm)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (he : (decodeHistory sources seed V l b e).Supported V outside)
    (hlarge : HistorySupportReduction.LargePrimes V
      (decodeHistory sources seed V l (giantState a Xp Xm) c))
    (klarge : HistorySupportReduction.LargePrimes V
      (decodeHistory sources seed V l (giantState b Xp Xm) e))
    (M : ℕ) [NeZero (pairModulus (decodeHistory sources seed V l a c)
      (decodeHistory sources seed V l b e) outside)]
    (hd : pairModulus (decodeHistory sources seed V l a c)
      (decodeHistory sources seed V l b e) outside ∣ M)
    (bcount scount : ℕ) (X tb td G : ℝ) :
    supportedHistoryPairXi d V outside bcount scount X tb td G
      (decodeHistory sources seed V l (giantState a Xp Xm) c)
      (decodeHistory sources seed V l (giantState b Xp Xm) e) =
    (by classical exact if Nat.Coprime Xp.natAbs Xm.natAbs then
      ((((decodeHistory sources seed V l a c).compensationProduct : ℂ) *
        ((decodeHistory sources seed V l b e).compensationProduct : ℂ)) *
      actualRealXi bcount scount X tb td G outside
        (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e) hc he
        (signedGiantSample (decodeHistory sources seed V l a c) Xp Xm)
        (signedGiantSample (decodeHistory sources seed V l b e) Xp Xm) *
      liftedResidueTest (residueTransform d) V outside
        (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e)
        M hd ((Xp : ZMod M),(Xm : ZMod M))) else 0) := by
  classical
  let h := decodeHistory sources seed V l a c
  let k := decodeHistory sources seed V l b e
  let h' := decodeHistory sources seed V l (giantState a Xp Xm) c
  let k' := decodeHistory sources seed V l (giantState b Xp Xm) e
  have hi := changed_supported_iff sources seed V outside l a c ha Xp Xm hlarge
  have ki := changed_supported_iff sources seed V outside l b e hb Xp Xm klarge
  rw [liftedResidueTest_intCast (residueTransform d) h k hc he M hd Xp Xm]
  by_cases hh : h'.Supported V outside ∧ k'.Supported V outside
  · have hhg := hi.mp hh.1
    have khg := ki.mp hh.2
    rw [ite_eq_left hhg.2.1, ite_eq_left ⟨hhg.2.2,khg.2.2⟩]
    exact supportedHistoryPairXi_changedGiants d sources seed V outside l a b c e ha hb
      Xp Xm hp.le hm.le hc he hh.1 hh.2 bcount scount X tb td G
  · rw [supportedHistoryPairXi_eq_zero_of_not d V outside bcount scount X tb td G h' k' hh]
    by_cases hcop : Nat.Coprime Xp.natAbs Xm.natAbs
    · rw [ite_eq_left hcop]
      by_cases hres : ResidueGuarded V outside (rebuild h Xp Xm) ∧
          ResidueGuarded V outside (rebuild k Xp Xm)
      · rw [ite_eq_left hres]
        have hz : actualRealXi bcount scount X tb td G outside h k hc he
            (signedGiantSample h Xp Xm) (signedGiantSample k Xp Xm) = 0 := by
          by_contra hz
          have hpi := actualXi_ne_zero_rebuild_positiveIntegral bcount scount X tb td G outside
            h k hc he Xp Xm hp hm hres.1.2.1 hres.2.2.1 hz
          exact hh ⟨hi.mpr ⟨hpi.1,hcop,hres.1⟩,ki.mpr ⟨hpi.2,hcop,hres.2⟩⟩
        change 0 = _ * actualRealXi bcount scount X tb td G outside h k hc he
          (signedGiantSample h Xp Xm) (signedGiantSample k Xp Xm) * _
        rw [hz,mul_zero,zero_mul]
      · rw [ite_eq_right hres,mul_zero]
    · rw [ite_eq_right hcop]

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI

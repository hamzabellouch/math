import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationSquares

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator

theorem residueGuarded_pair_iff_static {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlarge : LargePrimes V h) (klarge : LargePrimes V k) (Xp Xm : ℤ)
    (ho : OutsideUnits outside (rebuild h Xp Xm))
    (ko : OutsideUnits outside (rebuild k Xp Xm)) :
    (ResidueGuarded V outside (rebuild h Xp Xm) ∧ ResidueGuarded V outside (rebuild k Xp Xm)) ↔
      (RootSmallUnits h Xp Xm ∧ RootSmallUnits k Xp Xm ∧
       (rebuild h Xp Xm).IntegralGuard ∧ (rebuild k Xp Xm).IntegralGuard ∧
       FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild k Xp Xm) ∧
       PairNumeratorSquares h k Xp Xm) := by
  have hout : ∀q∈outside,Nat.Coprime Xp.natAbs q ∧ Nat.Coprime Xm.natAbs q := by
    simpa only [rebuild_root,GiantOutsideUnits] using ho.root
  have hra := residueRootCoprime_rebuild_iff h hs Xp Xm hout
  have kra := residueRootCoprime_rebuild_iff k ks Xp Xm hout
  have hag := arithmeticGuards_rebuild_iff h hs hlarge Xp Xm
  have kag := arithmeticGuards_rebuild_iff k ks klarge Xp Xm
  constructor
  · rintro ⟨hh,hk⟩
    have ha := hag.mp hh.2.2
    have ka := kag.mp hk.2.2
    exact ⟨hra.mp hh.1,kra.mp hk.1,hh.2.1,hk.2.1,ha.1,ka.1,
      (pairNumeratorSquares_iff h k Xp Xm).mpr ⟨ha.2.1,ka.2.1⟩⟩
  · rintro ⟨ha,ka,hi,ki,hf,kf,hsq⟩
    have hp := (pairNumeratorSquares_iff h k Xp Xm).mp hsq
    exact ⟨⟨hra.mpr ha,hi,hag.mpr ⟨hf,hp.1,ho.pivotOutsideCoprime⟩⟩,
      ⟨kra.mpr ka,ki,kag.mpr ⟨kf,hp.2,ko.pivotOutsideCoprime⟩⟩⟩

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI

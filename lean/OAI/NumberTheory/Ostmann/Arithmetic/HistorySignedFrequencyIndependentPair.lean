import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyIndependentSingle

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySupportReduction HistorySignedDecode HistorySignedNumerators
open HistorySignedResidueFactorization HistoryPairPattern HistoryPairRows

def independentFiniteFrequencyUnits (K : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2))) : Prop :=
  singleFiniteFrequencyUnits K (pairedFrequencyProduct h k) h
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)) z ∧
  singleFiniteFrequencyUnits K (pairedFrequencyProduct h k) k
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)) z

def independentFiniteLeafAdmissible (K : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2))) : Prop :=
  singleFiniteLeafAdmissible K (pairedFrequencyProduct h k) h
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)) z ∧
  singleFiniteLeafAdmissible K (pairedFrequencyProduct h k) k
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)) z

theorem independent_integral_frequency_iff_finite
    (K : ℕ) {l : ℕ} (h k : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k)
    (hlarge : LargePrimes V h) (klarge : LargePrimes V k)
    (hu : FrequencyUnits (pairedFrequencyProduct h k) h)
    (ku : FrequencyUnits (pairedFrequencyProduct h k) k) (hle : l≤K)
    (hx : ∀i : Occurrences h k, AncestorUnits h k
      (fun j => (pairSample h k j:ZMod (slot h k i).value)) i)
    (hV : ∀i : Occurrences h k,∀j≤l,V j<(slot h k i).value)
    (Xp Xm : ℤ) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild k Xp Xm).IntegralGuard ∧
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild k Xp Xm)) ↔
    (independentFiniteFrequencyUnits K h k (Xp,Xm) ∧ independentFiniteLeafAdmissible K h k (Xp,Xm) ∧
      OwnPrimeLines h k hs ks Xp Xm) := by
  let R := pairedFrequencyProduct h k
  let : NeZero R := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  have hF : ∀s∈h.frequencies,s.natAbs∣R :=
    fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)
  have kF : ∀s∈k.frequencies,s.natAbs∣R :=
    fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)
  have hh := single_integral_frequency_iff_finite K R h hs hlarge hu hF hle Xp Xm
  have kk := single_integral_frequency_iff_finite K R k ks klarge ku kF hle Xp Xm
  constructor
  · rintro ⟨hi,ki,hf,kf⟩
    have hctx := hh.mp ⟨hi,hf⟩
    have kctx := kk.mp ⟨ki,kf⟩
    exact ⟨⟨hctx.1,kctx.1⟩,⟨hctx.2.1,kctx.2.1⟩,
      ownPrimeLines_of_integralGuard h k hs ks hroot Xp Xm hi ki⟩
  · rintro ⟨⟨hctx,kctx⟩,⟨hev,kev⟩,hlines⟩
    have ho := pair_guardedOwnDivisibility_of_lines h k hs ks hroot Xp Xm hx hV hlines
    have hi := hh.mpr ⟨hctx,hev,ho.1⟩
    have ki := kk.mpr ⟨kctx,kev,ho.2⟩
    exact ⟨hi.1,ki.1,hi.2,ki.2⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI

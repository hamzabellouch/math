import OAI.NumberTheory.Ostmann.Characters.CharacterPhaseBounds
import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhase
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters

theorem initialPhase_frequency_ne_zero {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (s:ℤ) (hphase:initialPhase p χ a s≠0) (i:ι) :
    (s:ZMod (p i))≠0 := by
  intro hs
  apply hphase
  unfold initialPhase
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [initialUnary,hs,neg_zero,MulChar.map_zero,mul_zero,zero_mul]

theorem initialPhase_frequency_isCoprime {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (s:ℤ) (hphase:initialPhase p χ a s≠0) (i:ι) :
    IsCoprime s (p i:ℤ) :=
  ((ZMod.coe_int_isUnit_iff_isCoprime s (p i)).mp
    (isUnit_iff_ne_zero.mpr (initialPhase_frequency_ne_zero p χ a s hphase i))).symm

namespace HigherBiasSource.SourceTemplate
open Construction Preliminaries Template
attribute [local instance] Classical.propDecidable

theorem sourceSample_currentAtomSupport {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (hw:Function.Injective w) (s:ℤ) (t:HistoryReconstruction.Tree 0)
    (hphase:unitHistoryPhase k 0 (sourceWidth cfg m)
      (sourceUnitData cfg m ζ) (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
      (sourceSample cfg m w) s t≠0) :
    CurrentAtomSupport k 0 s
      (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) := by
  let x:=sourceSample cfg m w
  let p:=fun i => (x i).val
  let chi:=fun i => sourceCharacterData cfg m χ i (x i)
  let ctr:=fun i => sourceTranslationData cfg m a i (x i)
  let : ∀i,Fact (p i).Prime:=fun i => ⟨primeUpTo_prime (x i)⟩
  let : Nonempty (SourceConstituent cfg m):=⟨⟨(.word,true),⟨0,by change 0 < m + 1; omega⟩⟩⟩
  have hph:initialPhase p chi ctr s≠0 := by
    have hh:sampledHistoryPhase k 0 (sourceWidth cfg m) (sourceCharacterData cfg m χ)
        (sourceTranslationData cfg m a) x s t≠0 := (mul_ne_zero_iff.mp hphase).2
    simpa only [sampledHistoryPhase_zero] using hh
  have hs:s≠0 := by
    intro he
    subst s
    exact hph (initialPhase_zero p chi ctr)
  have hp:samplePrimeSupport (schedule k 0) (sourceWidth cfg m) x := by
    apply (sourceSample_primeSupport cfg m w).mpr
    intro i z hiz
    exact (Nat.coprime_primes (primeUpTo_prime (w i)) (primeUpTo_prime (w z))).mpr
      (fun he => hiz (hw (Subtype.ext he)))
  refine ⟨hs,constituentSampleState_pos _ _ x,
    ((samplePrimeSupport_iff _ _ x).mp hp).1,?_⟩
  intro i
  unfold constituentSampleState
  apply IsCoprime.prod_right
  intro z hz
  exact initialPhase_frequency_isCoprime p chi ctr s hph ⟨i,z⟩

end HigherBiasSource.SourceTemplate
end Ostmann.Characters

end

end OAI

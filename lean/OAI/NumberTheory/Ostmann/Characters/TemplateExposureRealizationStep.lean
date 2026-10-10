import OAI.NumberTheory.Ostmann.Characters.TemplateExposureRealizationCore

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open FrequencyExposure
attribute [local instance] Classical.propDecidable

theorem frequency_ne_zero (R:ℕ) [NeZero R] (s:ℤ) (hs:s.natAbs∣R) : s≠0 := by
  intro hz
  rw [hz,Int.natAbs_zero] at hs
  exact NeZero.ne R (Nat.zero_dvd.mp hs)

theorem exposureStep_matches (k K R j:ℕ) [NeZero R] (hj:j<K)
    (d:List Bool→Data R) (p:List Bool) (b:Bool) (h:PairedKnownStates k R)
    (C C':(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ)
    (t x:(ZMod (R^(K+2)))ˣ)
    (hXL:((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod (R^(K+2)))=x)
    (hXR:((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod (R^(K+2)))=
      (x⁻¹*t:(ZMod (R^(K+2)))ˣ))
    (hc:ContextMatches k R (j+1) h.1 C) (hc':ContextMatches k R (j+1) h.2 C')
    (hint:(d p).s∣(d p).v*copiedProduct k j false (installWords k (j+1) C z)-
      (d p).w*copiedProduct k j true (installWords k (j+1) C z))
    (hint':(d p).s'∣(d p).v'*copiedProduct k j false (installWords k (j+1) C' z)-
      (d p).w'*copiedProduct k j true (installWords k (j+1) C' z)) :
    ContextMatches k R j (exposureStep k K R d b j (p,h) t x).2.1
      (coordinateChild k j (!b) C (reconstructedPivot k j (installWords k (j+1) C z)
        (d p).s (d p).v (d p).w)) ∧
    ContextMatches k R j (exposureStep k K R d b j (p,h) t x).2.2
      (coordinateChild k j (!b) C' (reconstructedPivot k j (installWords k (j+1) C' z)
        (d p).s' (d p).v' (d p).w')) := by
  let red := ZMod.castHom (pow_dvd_pow R (by omega : j+3≤K+2)) (ZMod (R^(j+3)))
  have hL : red (x:ZMod (R^(K+2)))=
      ((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod (R^(j+3))) := by
    rw [← hXL]
    exact map_intCast red _
  have hR : red ((x⁻¹*t:(ZMod (R^(K+2)))ˣ):ZMod (R^(K+2)))=
      ((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod (R^(j+3))) := by
    rw [← hXR]
    exact map_intCast red _
  have hcEq : h.1 (j+1)=fun i=>(C i:ZMod (R^(j+3))) := funext hc
  have hcEq' : h.2 (j+1)=fun i=>(C' i:ZMod (R^(j+3))) := funext hc'
  have he := knownChild_actual (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega))
    k j (!b) (d p).s (d p).v (d p).w C z
    (frequency_ne_zero R _ (d p).divides)
    (ResidueDivision.frequency_power_divides R (d p).s (d p).divides (j+2)) hint
  have he' := knownChild_actual (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega))
    k j (!b) (d p).s' (d p).v' (d p).w' C' z
    (frequency_ne_zero R _ (d p).divides')
    (ResidueDivision.frequency_power_divides R (d p).s' (d p).divides' (j+2)) hint'
  constructor <;> intro i
  · simp only [exposureStep,dite_eq_left hj]
    change (Function.update h.1 j
      (knownChild (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega)) k j (!b)
        (d p).s (d p).v (d p).w (h.1 (j+1))
        (red (x:ZMod (R^(K+2))))
        (red ((x⁻¹*t:(ZMod (R^(K+2)))ˣ):ZMod (R^(K+2)))))) j i=_
    rw [Function.update_self,hcEq,hL,hR]
    exact congrFun he i
  · simp only [exposureStep,dite_eq_left hj]
    change (Function.update h.2 j
      (knownChild (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega)) k j (!b)
        (d p).s' (d p).v' (d p).w' (h.2 (j+1))
        (red (x:ZMod (R^(K+2))))
        (red ((x⁻¹*t:(ZMod (R^(K+2)))ˣ):ZMod (R^(K+2)))))) j i=_
    rw [Function.update_self,hcEq',hL,hR]
    exact congrFun he' i

end Ostmann.Characters.Template

end

end OAI

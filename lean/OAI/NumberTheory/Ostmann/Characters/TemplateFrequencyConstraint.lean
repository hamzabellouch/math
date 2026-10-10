import OAI.NumberTheory.Ostmann.Characters.PairedFrequencyProbability
import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedResidues

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def unitConvention {R:Type*} [Monoid R] (x:R) : Rˣ := if h:IsUnit x then h.unit else 1

theorem unitConvention_coe {R:Type*} [Monoid R] (x:R) (h:IsUnit x) :
    (unitConvention x:R)=x := by rw [unitConvention,dite_eq_left h]; exact h.unit_spec

def nodeCoefficient (k j:ℕ) (b:Bool) (s:ℤ)
    (C:(schedule k (j+1)).Slot→ℤ) : (ZMod s.natAbs)ˣ :=
  unitConvention (blockProduct k j b (fun i=>(C i:ZMod s.natAbs)))

theorem actual_integrality_rawSplit (k j:ℕ) (s v w:ℤ)
    (C:(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ)
    (XL XR:(ZMod s.natAbs)ˣ)
    (hXL:((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod s.natAbs)=XL)
    (hXR:((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod s.natAbs)=XR)
    (hCL:IsUnit (blockProduct k j true (fun i=>(C i:ZMod s.natAbs))))
    (hCR:IsUnit (blockProduct k j false (fun i=>(C i:ZMod s.natAbs))))
    (hint:s∣v*copiedProduct k j false (installWords k (j+1) C z)-
      w*copiedProduct k j true (installWords k (j+1) C z)) :
    rawSplitConstraint s.natAbs v w (nodeCoefficient k j true s C)
      (nodeCoefficient k j false s C) (XL*XR) XL := by
  have hz : ((v*copiedProduct k j false (installWords k (j+1) C z)-
      w*copiedProduct k j true (installWords k (j+1) C z):ℤ):ZMod s.natAbs)=0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa only [Int.natCast_natAbs,abs_dvd] using hint
  change ((v*blockProduct k j false (installWords k (j+1) C z)-
      w*blockProduct k j true (installWords k (j+1) C z):ℤ):ZMod s.natAbs)=0 at hz
  rw [blockProduct_installWords,blockProduct_installWords] at hz
  simp only [Int.cast_sub,Int.cast_mul,blockProduct,Int.cast_prod,hXL,hXR] at hz
  unfold rawSplitConstraint nodeCoefficient
  rw [unitConvention_coe _ hCL,unitConvention_coe _ hCR]
  have he : (XL*XR)/XL=XR := by simp only [mul_div_cancel_left]
  rw [he]
  apply sub_eq_zero.mp
  simpa only [blockProduct,mul_assoc] using hz

theorem nodeCoefficient_of_residues (N:ℕ) (k j:ℕ) (b:Bool) (s:ℤ) (hs:s.natAbs∣N)
    (C:(schedule k (j+1)).Slot→ℤ) :
    unitConvention (ZMod.castHom hs (ZMod s.natAbs)
      (blockProduct k j b (fun i=>(C i:ZMod N))))=nodeCoefficient k j b s C := by
  unfold nodeCoefficient
  congr 1
  simp only [blockProduct,map_prod,map_intCast]

end Ostmann.Characters.Template

end

end OAI

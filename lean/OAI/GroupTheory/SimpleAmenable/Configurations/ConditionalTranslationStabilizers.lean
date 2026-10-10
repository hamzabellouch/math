import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.FiveTrackGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConditionalTranslationStabilizers

variable {a m : ℕ}

theorem trackTranslation_conditional_commute (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → CutRing × CutRing)
    (hd : ∀ i, σ i ≠ i → d i = 0) :
    Commute (trackTranslation d) (conditionalHom U σ) := by
  have he := conditional_translation_conjugate U σ d 0 hd
  have hU : (⟨translate a (-0) ⁻¹' U.val,polygon_preimage_translate (-0) U.property⟩ :
      polygonAlgebra a) = U := by
    apply Subtype.ext
    ext p
    simp only [Set.mem_preimage,neg_zero,translate_zero]
  rw [hU] at he
  have hx := congrArg (fun z => z * trackTranslation d) he
  change _*_ = _*_
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hx.symm

theorem conditional_conjugation_support (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d e : Fin m → CutRing × CutRing)
    (hde : ∀ i, σ i ≠ i → d i = e i) :
    trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ =
      trackTranslation e * conditionalHom U σ * (trackTranslation e)⁻¹ := by
  have hc := trackTranslation_conditional_commute U σ (d-e) (by
    intro i hi
    change d i - e i = 0
    rw [hde i hi,sub_self])
  rw [trackTranslation_sub] at hc
  have hcomm : Commute (trackTranslation (a := a) d) (trackTranslation e) := by
    change _*_ = _*_
    rw [← trackTranslation_add,← trackTranslation_add,add_comm d e]
  have he := congrArg (fun z => trackTranslation e * z * (trackTranslation d)⁻¹) hc.eq
  rw [hcomm.inv_right.eq] at he
  have hh : trackTranslation e * ((trackTranslation e)⁻¹ * trackTranslation d * conditionalHom U σ) *
      (trackTranslation d)⁻¹ = trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ := by group
  rw [hh] at he
  convert he using 1; group

end ConditionalTranslationStabilizers

end SimpleAmenable
end
end

end OAI

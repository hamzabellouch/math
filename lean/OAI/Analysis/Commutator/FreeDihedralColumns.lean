import Mathlib
import OAI.Analysis.Commutator.FreeHilbertEntries
import OAI.Analysis.Commutator.FreeNormalizedColumns

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma norm_letterOf_unitary (i : Bool) (u : unitary A)
    (hu : (u:A)∈S i) (hu0 : t.functional (u:A)=0) :
    ‖letterOf t S i (u:A) hu hu0‖=1 := by
  change ‖t.functional.toPreGNS (u:A)‖=1
  rw [PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [Unitary.star_mul_self_of_mem u.property,t.normalized,Complex.one_re,Real.sqrt_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma dihedral_negative_wave (d s : unitary A)
    (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1) (n : ℕ) :
    wave (d*s) (-(n:ℤ))=((s:A)*(d:A))^n := by
  have hd : d⁻¹=d := inv_eq_of_mul_eq_one_right (Subtype.ext hd2)
  have hs : s⁻¹=s := inv_eq_of_mul_eq_one_right (Subtype.ext hs2)
  rw [wave,zpow_neg,zpow_natCast,←inv_pow,mul_inv_rev,hd,hs]
  simp only [Submonoid.coe_mul,SubmonoidClass.coe_pow]

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable (e : D) (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e‖)

include hd2 hs2 in
theorem normalizedColumn_eq_dihedral (n : ℕ) :
    (normalizedColumn t S f hf hS hfree Bool.false_ne_true e
      (letterOf t S true (s:A) hs hs0) (norm_letterOf_unitary t S true s hs hs0)
      (letterOf t S false (d:A) hd hd0) (norm_letterOf_unitary t S false d hd hd0) hr n
      ).toContinuousLinearMap=
    dihedralColumn t S hfree (f e) (d*s)
      ‖TracialGNS.algebraVector (factorTrace t f hf) e‖⁻¹ n := by
  apply ContinuousLinearMap.ext
  intro v
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v =>
    change normalizedColumn t S f hf hS hfree Bool.false_ne_true e
      (letterOf t S true (s:A) hs hs0) (norm_letterOf_unitary t S true s hs hs0)
      (letterOf t S false (d:A) hd hd0) (norm_letterOf_unitary t S false d hd hd0) hr n
        (v : multiplicityLevel t S true 0)=_
    rw [normalizedColumn_apply,repeatedOutput_bounded]
    rw [letterValue_letterOf,letterValue_letterOf]
    rw [dihedralColumn_coe,dihedral_negative_wave d s hd2 hs2]
    change (_:ℂ) • t.functional.gnsStarAlgHom (f e)
      (t.functional.gnsStarAlgHom (((s:A)*(d:A))^n)
        (baseEmbedding t S hfree (v : multiplicityLevel t S true 0)))=_
    rw [baseEmbedding_coe,TracialGNS.left_coe,TracialGNS.left_coe]
    apply congrArg (fun a : A =>
      ((‖TracialGNS.algebraVector (factorTrace t f hf) e‖⁻¹:ℝ):ℂ) •
        (t.functional.toPreGNS a : t.functional.GNS))
    exact (mul_assoc _ _ _).symm

end Kadison.FreeBlocks

end

end
end

end OAI

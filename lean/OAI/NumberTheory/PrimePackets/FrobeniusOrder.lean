import Mathlib

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
attribute [local instance] Ideal.Quotient.field
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

omit [FiniteDimensional F E] in
lemma isArithFrobAt_restrict_pow_mk
    (Q : Ideal (𝓞 E)) (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q)
    (n : ℕ) (x : 𝓞 E) :
    Ideal.Quotient.mk Q ((σ ^ n) • x) =
      (H.restrict ^ n) (Ideal.Quotient.mk Q x) := by
  induction n with
  | zero => simp only [pow_zero, one_smul, AlgHom.one_apply]
  | succ n ih =>
    rw [pow_succ', mul_smul]
    change Ideal.Quotient.mk Q ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 E) σ)
      ((σ ^ n) • x)) = _
    rw [← H.restrict_mk, ih, pow_succ', AlgHom.mul_apply]

 

omit [FiniteDimensional F E] in
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q) :
    orderOf σ = Q.inertiaDeg (𝓞 F) := by
  let : FaithfulSMul (E ≃ₐ[F] E) (𝓞 E) := IsGaloisGroup.faithful (𝓞 F)
  have horder : orderOf σ = orderOf H.restrict := by
    apply orderOf_eq_orderOf_iff.mpr
    intro n
    constructor
    · intro hn
      apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← isArithFrobAt_restrict_pow_mk F E Q σ H n x, hn, one_smul]
      rfl
    · intro hn
      have Hn : IsArithFrobAt (𝓞 F) (σ ^ (n + 1)) Q := by
        intro x
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, map_pow]
        change Ideal.Quotient.mk Q ((σ ^ (n + 1)) • x) -
          Ideal.Quotient.mk Q x ^ Nat.card ((𝓞 F) ⧸ Q.under (𝓞 F)) = 0
        rw [isArithFrobAt_restrict_pow_mk F E Q σ H, pow_succ, hn, one_mul,
          H.restrict_apply, sub_self]
      have he : σ ^ (n + 1) = σ := by
        apply MulSemiringAction.toAlgHom_injective (𝓞 F) (𝓞 E)
        exact Hn.eq_of_isUnramifiedAt H Q.primeCompl_le_nonZeroDivisors
      exact mul_right_cancel (by simpa only [pow_succ, one_mul] using he :
        σ ^ n * σ = 1 * σ)
  let : (Q.under (𝓞 F)).IsMaximal := by
    rw [← Q.over_def P]
    infer_instance
  let : Fintype ((𝓞 F) ⧸ Q.under (𝓞 F)) := Fintype.ofFinite _
  have hr : H.restrict = FiniteField.frobeniusAlgHom
      ((𝓞 F) ⧸ Q.under (𝓞 F)) ((𝓞 E) ⧸ Q) := by
    ext x
    simp only [H.restrict_apply, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [horder, hr, FiniteField.orderOf_frobeniusAlgHom,
    Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 F)) Q]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI

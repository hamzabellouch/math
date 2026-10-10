import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusCoset

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical Pointwise
namespace PrimeDegreePackets.GaloisIdealCharacter
 

theorem actual_frobenius_tower
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    ∃ τ : E ≃ₐ[L] E,
      τ.restrictScalars F = g ^ (Q.under (𝓞 L)).inertiaDeg (𝓞 F) ∧
      IsArithFrobAt (𝓞 L) τ Q := by
  let C := Subgroup.zpowers g
  let x : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup := QuotientGroup.mk 1
  let D := MulAction.stabilizer C x
  let c : C := ⟨g, Subgroup.mem_zpowers g⟩
  have hfixOrbit : g ^ Nat.card (MulAction.orbit C x) ∈ L.fixingSubgroup := by
    have hc := D.pow_index_mem c
    have hcardC : D.index = Nat.card (MulAction.orbit C x) :=
      (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C x)).symm
    rw [hcardC] at hc
    have hs := MulAction.mem_stabilizer_iff.mp hc
    change (QuotientGroup.mk (g ^ Nat.card (MulAction.orbit C x) * 1) :
      (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) = QuotientGroup.mk 1 at hs
    simpa using (QuotientGroup.eq.mp hs.symm)
  have hcard : Nat.card (MulAction.orbit C x) = (Q.under (𝓞 L)).inertiaDeg (𝓞 F) := by
    have he : C = MulAction.stabilizer (E ≃ₐ[F] E) Q :=
      zpowers_frobenius_eq_stabilizer F E P Q g hg
    have ho : MulAction.orbit C x =
        MulAction.orbit (MulAction.stabilizer (E ≃ₐ[F] E) Q) x := by
      ext y
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨⟨a.val, he ▸ a.property⟩, ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨⟨a.val, he.symm ▸ a.property⟩, ha⟩
    calc
      _ = Nat.card (MulAction.orbit (MulAction.stabilizer (E ≃ₐ[F] E) Q) x) :=
        by rw [ho]
      _ = _ := by simpa only [x, inv_one, one_smul] using
        cosetOrbit_card_eq_inertiaDeg F E L P hP Q 1
  rw [hcard] at hfixOrbit
  let τ : E ≃ₐ[L] E := IntermediateField.fixingSubgroupEquiv L ⟨_, hfixOrbit⟩
  refine ⟨τ, rfl, ?_⟩
  let R := Q.under (𝓞 L)
  let : R.IsPrime := inferInstance
  let : R.LiesOver P := by
    constructor
    rw [Ideal.under_under, Q.over_def P]
  let : R.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP R)
  have hnorm : Nat.card ((𝓞 L) ⧸ R) =
      Nat.card ((𝓞 F) ⧸ P) ^ R.inertiaDeg (𝓞 F) := by
    change Ideal.absNorm R = Ideal.absNorm P ^ R.inertiaDeg (𝓞 F)
    exact (Ideal.absNorm_pow_inertiaDeg P R).symm
  have hpow (k : ℕ) (y : 𝓞 E) :
      Ideal.Quotient.mk Q ((g^k) • y) =
        (Ideal.Quotient.mk Q y) ^ (Nat.card ((𝓞 F) ⧸ P))^k := by
    induction k with
    | zero => simp only [pow_zero, one_smul, pow_one]
    | succ k ih =>
      rw [pow_succ', mul_smul]
      change Ideal.Quotient.mk Q ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 E) g)
        ((g ^ k) • y)) = _
      rw [hg.mk_apply, ← Q.over_def P, ih, ← pow_mul, pow_succ]
  intro y
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_pow]
  change Ideal.Quotient.mk Q ((g ^ R.inertiaDeg (𝓞 F)) • y) -
    (Ideal.Quotient.mk Q y) ^ Nat.card ((𝓞 L) ⧸ R) = 0
  rw [hpow, hnorm, sub_self]
end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI

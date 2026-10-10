import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusOrder

namespace OAI

noncomputable section
open Module
open scoped NumberField Pointwise Classical
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

lemma zpowers_frobenius_eq_stabilizer
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    Subgroup.zpowers g = MulAction.stabilizer (E ≃ₐ[F] E) Q := by
  have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (E ≃ₐ[F] E) Q :=
    Subgroup.zpowers_le.mpr hg.mem_stabilizer
  have hc : Nat.card (Subgroup.zpowers g) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) Q) := by
    rw [Nat.card_zpowers, orderOf_eq_inertiaDeg_of_isArithFrobAt F E P Q g hg,
      Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P Q (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]
  exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion hle)).mpr
        ⟨Set.inclusion_injective hle, hc⟩).2)

local instance fixingRingGroup (L : IntermediateField F E) :
    IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
  IsGaloisGroup.of_mulEquiv (IntermediateField.fixingSubgroupEquiv L)
    (fun _ _ => rfl)

local instance fixingRingCommutes (L : IntermediateField F E) :
    SMulCommClass L.fixingSubgroup (𝓞 L) (𝓞 E) :=
  (fixingRingGroup F E L).commutes

omit [FiniteDimensional F E] in
lemma under_fixing_smul (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (h : L.fixingSubgroup) :
    ((h.val : E ≃ₐ[F] E) • Q).under (𝓞 L) = Q.under (𝓞 L) := by
  change (h • Q).under (𝓞 L) = _
  exact Ideal.under_smul (𝓞 L) Q h

def cosetPrime (L : IntermediateField F E) (Q : Ideal (𝓞 E)) :
    (E ≃ₐ[F] E) ⧸ L.fixingSubgroup → Ideal (𝓞 L) := by
  refine Quotient.lift (fun a : E ≃ₐ[F] E => (a⁻¹ • Q).under (𝓞 L)) ?_
  intro a b hab
  have hm : a⁻¹ * b ∈ L.fixingSubgroup := QuotientGroup.leftRel_apply.mp hab
  have he : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
  rw [he, mul_smul]
  exact (under_fixing_smul F E L (a⁻¹ • Q) ⟨(a⁻¹ * b)⁻¹, L.fixingSubgroup.inv_mem hm⟩).symm

omit [FiniteDimensional F E] in
@[simp] lemma cosetPrime_mk (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (a : E ≃ₐ[F] E) :
    cosetPrime F E L Q (QuotientGroup.mk a) = (a⁻¹ • Q).under (𝓞 L) := rfl

omit [FiniteDimensional F E] in
lemma cosetPrime_stabilizer_smul (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (h : MulAction.stabilizer (E ≃ₐ[F] E) Q)
    (a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q (h • a) = cosetPrime F E L Q a := by
  induction a using Quotient.inductionOn
  rename_i a
  change ((h.val * a)⁻¹ • Q).under (𝓞 L) = _
  rw [mul_inv_rev, mul_smul]
  have : h.val⁻¹ • Q = Q := h⁻¹ |>.property
  rw [this]
  rfl

section GroupCosets
variable {G A : Type*} [Group G] [MulAction G A]

lemma mem_coset_stabilizer_iff (H : Subgroup G) (x : A) (a : G)
    (d : MulAction.stabilizer G x) :
    d ∈ MulAction.stabilizer (MulAction.stabilizer G x) (QuotientGroup.mk a : G ⧸ H) ↔
      a⁻¹ * d.val * a ∈ H := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (d.val * a) : G ⧸ H) = QuotientGroup.mk a ↔ _
  rw [eq_comm, QuotientGroup.eq]
  simp only [mul_assoc]

 

def cosetStabilizerEquiv (H : Subgroup G) (x : A) (a : G) :
    MulAction.stabilizer (MulAction.stabilizer G x) (QuotientGroup.mk a : G ⧸ H) ≃
      MulAction.stabilizer H (a⁻¹ • x) where
  toFun d := ⟨⟨a⁻¹ * d.val.val * a, (mem_coset_stabilizer_iff H x a d.val).mp d.property⟩,
    by
      change (a⁻¹ * d.val.val * a) • (a⁻¹ • x) = a⁻¹ • x
      rw [mul_smul, mul_smul, smul_inv_smul, d.val.property]⟩
  invFun h := ⟨⟨a * h.val.val * a⁻¹, by
      change (a * h.val.val * a⁻¹) • x = x
      rw [mul_smul, mul_smul]
      rw [show h.val.val • (a⁻¹ • x) = a⁻¹ • x from h.property, smul_inv_smul]⟩, by
    apply (mem_coset_stabilizer_iff H x a _).mpr
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.val.property⟩
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change a * (a⁻¹ * d.val.val * a) * a⁻¹ = d.val.val
    group
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    change a⁻¹ * (a * h.val.val * a⁻¹) * a = h.val.val
    group
end GroupCosets

lemma cosetPrime_eq_iff (L : IntermediateField F E) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (a b : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q a = cosetPrime F E L Q b ↔
      MulAction.orbitRel (MulAction.stabilizer (E ≃ₐ[F] E) Q) _ a b := by
  constructor
  · induction a using Quotient.inductionOn
    rename_i a
    induction b using Quotient.inductionOn
    rename_i b
    intro he
    change (a⁻¹ • Q).under (𝓞 L) = (b⁻¹ • Q).under (𝓞 L) at he
    let : (a⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
    let : (b⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
    obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (𝓞 L) (𝓞 E) L.fixingSubgroup (b⁻¹ • Q) (a⁻¹ • Q) he.symm
    have hd : a * h.val * b⁻¹ ∈ MulAction.stabilizer (E ≃ₐ[F] E) Q := by
      change (a * h.val * b⁻¹) • Q = Q
      rw [mul_smul, mul_smul]
      rw [show h.val • (b⁻¹ • Q) = a⁻¹ • Q from hh.symm, smul_inv_smul]
    refine ⟨⟨a * h.val * b⁻¹, hd⟩, ?_⟩
    change (QuotientGroup.mk ((a * h.val * b⁻¹) * b) : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) =
      QuotientGroup.mk a
    rw [eq_comm, QuotientGroup.eq]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.property
  · rintro ⟨h, rfl⟩
    exact cosetPrime_stabilizer_smul F E L Q h b

omit [FiniteDimensional F E] in
lemma cosetPrime_mem_primesOver (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P]
    (a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q a ∈ Ideal.primesOver P (𝓞 L) := by
  induction a using Quotient.inductionOn
  rename_i a
  change (a⁻¹ • Q).under (𝓞 L) ∈ _
  let : (a⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  let : (a⁻¹ • Q).LiesOver P := Ideal.LiesOver.smul _
  refine ⟨inferInstance, ?_⟩
  constructor
  rw [Ideal.under_under, (a⁻¹ • Q).over_def P]

def primeOfCosetOrbit (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P] :
    MulAction.orbitRel.Quotient (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup) → Ideal.primesOver P (𝓞 L) := by
  refine Quotient.lift (fun a =>
    ⟨cosetPrime F E L Q a, cosetPrime_mem_primesOver F E L P Q a⟩) ?_
  intro a b h
  apply Subtype.ext
  exact (cosetPrime_eq_iff F E L Q a b).mpr h

lemma primeOfCosetOrbit_bijective (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    Function.Bijective (primeOfCosetOrbit F E L P Q) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn
    rename_i a
    induction b using Quotient.inductionOn
    rename_i b
    intro hab
    apply Quotient.sound
    apply (cosetPrime_eq_iff F E L Q a b).mp
    exact congrArg Subtype.val hab
  · intro R
    let : R.val.IsPrime := R.property.1
    let : R.val.LiesOver P := R.property.2
    let S : Ideal.primesOver R.val (𝓞 E) := Classical.choice inferInstance
    let : S.val.IsPrime := S.property.1
    let : S.val.LiesOver R.val := S.property.2
    let : S.val.LiesOver P := Ideal.LiesOver.trans S.val R.val P
    obtain ⟨a, ha⟩ := Ideal.exists_smul_eq_of_isGaloisGroup P Q S.val (E ≃ₐ[F] E)
    refine ⟨Quotient.mk _ (QuotientGroup.mk a⁻¹), ?_⟩
    apply Subtype.ext
    change (a⁻¹⁻¹ • Q).under (𝓞 L) = R.val
    rw [inv_inv, ha]
    exact (S.val.over_def R.val).symm

lemma cosetOrbit_card_eq_inertiaDeg
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q] (a : E ≃ₐ[F] E) :
    Nat.card (MulAction.orbit (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      (QuotientGroup.mk a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup)) =
      ((a⁻¹ • Q).under (𝓞 L)).inertiaDeg (𝓞 F) := by
  let Q' : Ideal (𝓞 E) := a⁻¹ • Q
  let R : Ideal (𝓞 L) := Q'.under (𝓞 L)
  let : Q'.IsPrime := Ideal.IsPrime.smul _
  let : Q'.LiesOver P := Ideal.LiesOver.smul _
  let : Q'.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q')
  let : R.IsPrime := inferInstance
  let : Q'.LiesOver R := inferInstance
  let : R.LiesOver P := by
    constructor
    rw [Ideal.under_under, Q'.over_def P]
  let : R.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP R)
  have heQ' : Q'.ramificationIdx (𝓞 F) = 1 := by
    change (a⁻¹ • Q).ramificationIdx (𝓞 F) = 1
    rw [Ideal.ramificationIdx_smul, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  have he : Q'.ramificationIdx (𝓞 L) = 1 := by
    have h := Ideal.ramificationIdx_tower (R := 𝓞 F) R Q'
    rw [heQ'] at h
    exact Nat.eq_one_of_mul_eq_one_left h.symm
  have hlocal : Nat.card (MulAction.stabilizer L.fixingSubgroup Q') =
      Q'.inertiaDeg (𝓞 L) := by
    have hc := Ideal.card_stabilizer_eq (G := L.fixingSubgroup) R Q'
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx R Q' L.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg R Q' L.fixingSubgroup, he, one_mul] at hc
    convert hc using 1
    congr 1
  have hbase : Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) Q) =
      Q.inertiaDeg (𝓞 F) := by
    rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P Q (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]
  have hstab := Nat.card_congr (cosetStabilizerEquiv L.fixingSubgroup Q a)
  have hc := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      (QuotientGroup.mk a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup))
  rw [Nat.card_prod, hstab, hlocal, hbase] at hc
  have hf : Q.inertiaDeg (𝓞 F) = R.inertiaDeg (𝓞 F) * Q'.inertiaDeg (𝓞 L) := by
    rw [← Ideal.inertiaDeg_smul (𝓞 F) Q a⁻¹]
    exact Ideal.inertiaDeg_tower R Q'
  apply Nat.eq_of_mul_eq_mul_right (Ideal.inertiaDeg_pos Q' (𝓞 L))
  exact hc.trans hf

 

theorem actual_frobenius_coset_cycle_lengths
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    ∃ e : MulAction.orbitRel.Quotient (Subgroup.zpowers g)
        ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup) ≃ Ideal.primesOver P (𝓞 L),
      ∀ o, Nat.card o.orbit = (e o).val.inertiaDeg (𝓞 F) := by
  rw [zpowers_frobenius_eq_stabilizer F E P Q g hg]
  refine ⟨Equiv.ofBijective (primeOfCosetOrbit F E L P Q)
    (primeOfCosetOrbit_bijective F E L P Q), ?_⟩
  intro o
  induction o using Quotient.inductionOn
  rename_i a
  induction a using Quotient.inductionOn
  rename_i a
  exact cosetOrbit_card_eq_inertiaDeg F E L P hP Q a

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI

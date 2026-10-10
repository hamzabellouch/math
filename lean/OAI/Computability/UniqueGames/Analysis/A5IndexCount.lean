import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Analysis.OperatorPartitions

namespace OAI

section

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A5IndexCount

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

def insideEquiv (A I : Submodule F2 V) (hIA : I ≤ A) :
    (I.comap A.subtype) ≃ₗ[F2] I where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hIA i.property⟩, i.property⟩
  left_inv _i := Subtype.ext (Subtype.ext rfl)
  right_inv _i := Subtype.ext rfl
  map_add' _i _j := Subtype.ext rfl
  map_smul' _c _i := Subtype.ext rfl

theorem internal_isCompl (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) :
    IsCompl (I.comap A.subtype) (A0.comap A.subtype) := by
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro a hi h0
    exact Subtype.ext (Submodule.disjoint_def.mp hd a.val h0 hi)
  · apply eq_top_iff.mpr
    intro a _
    have ha : a.val ∈ A0 ⊔ I := by rw [hj]; exact a.property
    rcases Submodule.mem_sup.mp ha with ⟨v, hv, i, hi, hvi⟩
    refine Submodule.mem_sup.mpr ⟨⟨i, hIA hi⟩, hi, ⟨v, hA0 hv⟩, hv, ?_⟩
    apply Subtype.ext
    change i + v = a.val
    rw [add_comm]
    exact hvi

def projectionA0 (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) : A →ₗ[F2] I :=
  (insideEquiv A I hIA).toLinearMap.comp
    (((I.comap A.subtype).isComplEquivProj
      ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩).val)

theorem projectionA0_injective (A I A0 A0' : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A)
    (hd' : Disjoint A0' I) (hj' : A0' ⊔ I = A)
    (h : projectionA0 A I A0 hIA hd hj = projectionA0 A I A0' hIA hd' hj') :
    A0 = A0' := by
  let P := I.comap A.subtype
  let Q : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩
  let Q' : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0'.comap A.subtype, internal_isCompl A I A0' hIA hd' hj'⟩
  have hp : (P.isComplEquivProj Q).val = (P.isComplEquivProj Q').val := by
    apply LinearMap.ext
    intro a
    apply (insideEquiv A I hIA).injective
    exact LinearMap.congr_fun h a
  have hQ := P.isComplEquivProj.injective (Subtype.ext hp)
  have hq : A0.comap A.subtype = A0'.comap A.subtype := congrArg Subtype.val hQ
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  have hA0' : A0' ≤ A := le_sup_left.trans hj'.le
  ext x
  constructor
  · intro hx
    have hm : (⟨x, hA0 hx⟩ : A) ∈ A0.comap A.subtype := hx
    rw [hq] at hm
    exact hm
  · intro hx
    have hm : (⟨x, hA0' hx⟩ : A) ∈ A0'.comap A.subtype := hx
    rw [← hq] at hm
    exact hm

def fullRange {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    L →ₗ[F2] S.range :=
  (LinearMap.id : L →ₗ[F2] L).codRestrict S.range (fun x => by rw [hS]; trivial)

theorem fullRange_surjective {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    Function.Surjective (fullRange S hS) := fun c => ⟨c.val, Subtype.ext rfl⟩

theorem quotientRestriction_surjective (J B0 : Submodule F2 W) (hc : B0 ⊔ J = ⊤) :
    Function.Surjective (A4IndexCount.quotientRestriction J B0) := by
  intro z
  obtain ⟨w, rfl⟩ := J.mkQ_surjective z
  have hw : w ∈ B0 ⊔ J := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, j, hj, hbj⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change J.mkQ b = J.mkQ w
  have hz : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hj
  rw [← hbj, map_add, hz, add_zero]

theorem quotientRestriction_same_kernel (B J B0 : Submodule F2 W)
    (hm : B0 ⊓ J = B) :
    (A4IndexCount.quotientRestriction J B0).ker =
      (A4IndexCount.quotientRestriction B B0).ker := by
  rw [A4IndexCount.ker_quotientRestriction, A4IndexCount.ker_quotientRestriction]
  ext b
  change (b : W) ∈ J ↔ (b : W) ∈ B
  constructor
  · intro hj
    have hb : (b : W) ∈ B0 ⊓ J := ⟨b.property, hj⟩
    rwa [hm] at hb
  · intro hb
    exact (hm.symm.le.trans inf_le_right) hb

def sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) : (W ⧸ J) →ₗ[F2] (W ⧸ B) :=
  (A4IndexCount.factorViaRange (A4IndexCount.quotientRestriction J B0)
    (A4IndexCount.quotientRestriction B B0)
    (quotientRestriction_same_kernel B J B0 hm).le).comp
      (fullRange (A4IndexCount.quotientRestriction J B0)
        (LinearMap.range_eq_top.mpr (quotientRestriction_surjective J B0 hc)))

theorem range_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range = (A4IndexCount.quotientRestriction B B0).range := by
  rw [sectionB0, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (fullRange_surjective _ _))]
  exact A4IndexCount.factorViaRange_range _ _ _

theorem recover_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range.comap B.mkQ = B0 := by
  rw [range_sectionB0]
  have hB : B ≤ B0 := hm.symm.le.trans inf_le_left
  ext w
  change B.mkQ w ∈ (A4IndexCount.quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hz : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hz) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem sectionB0_injective (B J B0 B0' : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B)
    (hc' : B0' ⊔ J = ⊤) (hm' : B0' ⊓ J = B)
    (h : sectionB0 B J B0 hc hm = sectionB0 B J B0' hc' hm') : B0 = B0' := by
  calc
    B0 = (sectionB0 B J B0 hc hm).range.comap B.mkQ :=
      (recover_sectionB0 B J B0 hc hm).symm
    _ = (sectionB0 B J B0' hc' hm').range.comap B.mkQ :=
      congrArg (fun T : (W ⧸ J) →ₗ[F2] (W ⧸ B) => T.range.comap B.mkQ) h
    _ = B0' := recover_sectionB0 B J B0' hc' hm'

def encode (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) (p : OperatorPartitions.A5GeometricIndex X A B) :
    (A →ₗ[F2] X.range) × ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) :=
  (projectionA0 A X.range p.val.1 hIA p.property.1 p.property.2.1,
    sectionB0 B X.ker p.val.2 p.property.2.2.1 p.property.2.2.2)

theorem encode_injective (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) : Function.Injective (encode X A B hIA) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact projectionA0_injective A X.range p.val.1 q.val.1 hIA
      p.property.1 p.property.2.1 q.property.1 q.property.2.1 (congrArg Prod.fst h)
  · exact sectionB0_injective B X.ker p.val.2 q.val.2
      p.property.2.2.1 p.property.2.2.2 q.property.2.2.1 q.property.2.2.2
      (congrArg Prod.snd h)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_geometricIndex_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B))) := by
  have hfirst := CompressionCount.natCard_linearMap (U := A) (C := X.range)
  have hsecond := CompressionCount.natCard_linearMap (U := W ⧸ X.ker) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] X.range) := Nat.finite_of_card_ne_zero
    (by rw [hfirst]; exact pow_ne_zero _ (by decide))
  let : Finite ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero
    (by rw [hsecond]; exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode X A B hIA) (encode_injective X A B hIA)
  rw [Nat.card_prod, hfirst, hsecond, X.quotKerEquivRange.finrank_eq, ← pow_add] at h
  have he : Module.finrank F2 A * Module.finrank F2 X.range +
      Module.finrank F2 X.range * Module.finrank F2 (W ⧸ B) =
      Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) := by ring
  rwa [he] at h

theorem card_geometricIndex_degree_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (2 * d * Module.finrank F2 X.range) := by
  have hs : Module.finrank F2 A + Module.finrank F2 (W ⧸ B) ≤ 2 * d := by omega
  have he : Module.finrank F2 X.range *
      (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) ≤
      2 * d * Module.finrank F2 X.range := by
    calc
      _ ≤ Module.finrank F2 X.range * (2 * d) := Nat.mul_le_mul_left _ hs
      _ = _ := by ac_rfl
  exact (card_geometricIndex_le X A B hIA).trans
    (Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) he)

theorem card_geometricIndex_cube_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ^ 3 ≤
      2 ^ (6 * d * Module.finrank F2 X.range) := by
  have h := Nat.pow_le_pow_left (card_geometricIndex_degree_le X A B hIA d hA hB) 3
  rw [← pow_mul] at h
  convert h using 1
  congr 1
  ring

end UniqueGamesTheorem.Appendix.A5IndexCount

end

end

end OAI

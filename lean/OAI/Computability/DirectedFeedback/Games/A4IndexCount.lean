import Mathlib
import OAI.Computability.DirectedFeedback.Games.Derivatives

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

def factorViaRange {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    X.range →ₗ[K] T :=
  (X.ker.liftQ P hker).comp X.quotKerEquivRange.symm.toLinearMap

theorem factorViaRange_apply {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) (u : U) :
    factorViaRange X P hker (X.rangeRestrict u) = P u := by
  have hq : X.quotKerEquivRange.symm (X.rangeRestrict u) = X.ker.mkQ u :=
    X.quotKerEquivRange.symm_apply_apply (X.ker.mkQ u)
  dsimp only [factorViaRange, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hq]
  rfl

theorem factorViaRange_injective {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker = P.ker) :
    Function.Injective (factorViaRange X P hker.le) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := X.surjective_rangeRestrict a
  obtain ⟨v, rfl⟩ := X.surjective_rangeRestrict b
  rw [factorViaRange_apply, factorViaRange_apply] at hab
  have hp : u - v ∈ P.ker := by
    change P (u - v) = 0
    rw [map_sub, hab, sub_self]
  have hx : u - v ∈ X.ker := by rwa [hker]
  apply Subtype.ext
  apply sub_eq_zero.mp
  change X u - X v = 0
  simpa only [LinearMap.mem_ker, map_sub] using hx

theorem factorViaRange_range {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    (factorViaRange X P hker).range = P.range := by
  have hc : (factorViaRange X P hker).comp X.rangeRestrict = P := by
    apply LinearMap.ext
    intro u
    exact factorViaRange_apply X P hker u
  calc
    _ = ((factorViaRange X P hker).comp X.rangeRestrict).range :=
      (LinearMap.range_comp_of_range_eq_top _ X.range_rangeRestrict).symm
    _ = _ := congrArg LinearMap.range hc

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def quotientRestriction (B B0 : Submodule K W) : B0 →ₗ[K] (W ⧸ B) :=
  B.mkQ.comp B0.subtype

theorem ker_quotientRestriction (B B0 : Submodule K W) :
    (quotientRestriction B B0).ker = B.comap B0.subtype := by
  ext b
  change B.mkQ (b : W) = 0 ↔ (b : W) ∈ B
  exact Submodule.Quotient.mk_eq_zero B

def aToRange (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) : A →ₗ[K] X.range :=
  (A0.mkQ.comp A.subtype).codRestrict X.range (by
    intro a
    rw [hR]
    exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩)

theorem aToRange_surjective (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) :
    Function.Surjective (aToRange A A0 B0 X hR) := by
  intro c
  have hc : (c : V ⧸ A0) ∈ A.map A0.mkQ := by rw [← hR]; exact c.property
  rcases Submodule.mem_map.mp hc with ⟨a, ha, he⟩
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

def encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) : A →ₗ[K] (W ⧸ B) :=
  (factorViaRange X (quotientRestriction B B0)
    (hK.trans (ker_quotientRestriction B B0).symm).le).comp
      (aToRange A A0 B0 X hR)

theorem encodeFixed_relation (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (a : A) (b : B0) :
    encodeFixed A A0 B B0 X hK hR a = B.mkQ (b : W) ↔ A0.mkQ (a : V) = X b := by
  let P := quotientRestriction B B0
  have hXP : X.ker = P.ker := hK.trans (ker_quotientRestriction B B0).symm
  change factorViaRange X P hXP.le (aToRange A A0 B0 X hR a) = P b ↔ _
  rw [← factorViaRange_apply X P hXP.le b,
    (factorViaRange_injective X P hXP).eq_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

theorem ker_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).ker = A0.comap A.subtype := by
  ext a
  have h := encodeFixed_relation A A0 B B0 X hK hR a (0 : B0)
  simpa using h

theorem range_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).range = (quotientRestriction B B0).range := by
  rw [encodeFixed, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (aToRange_surjective A A0 B0 X hR))]
  exact factorViaRange_range _ _ _

theorem recover_A0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hA : A0 ≤ A) :
    (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype = A0 := by
  rw [ker_encodeFixed]
  ext a
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    exact Submodule.mem_map.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem recover_B0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hB : B ≤ B0) :
    (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ = B0 := by
  rw [range_encodeFixed]
  ext w
  change B.mkQ w ∈ (quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hm : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hm) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem encodeFixed_injective (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X X' : B0 →ₗ[K] (V ⧸ A0))
    (hK : X.ker = B.comap B0.subtype) (hR : X.range = A.map A0.mkQ)
    (hK' : X'.ker = B.comap B0.subtype) (hR' : X'.range = A.map A0.mkQ)
    (h : encodeFixed A A0 B B0 X hK hR = encodeFixed A A0 B B0 X' hK' hR') : X = X' := by
  apply LinearMap.ext
  intro b
  have hb : X b ∈ A.map A0.mkQ := by rw [← hR]; exact ⟨b, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨a, ha, he⟩
  have henc : encodeFixed A A0 B B0 X hK hR ⟨a, ha⟩ = B.mkQ (b : W) :=
    (encodeFixed_relation A A0 B B0 X hK hR ⟨a, ha⟩ b).mpr he
  have henc' : encodeFixed A A0 B B0 X' hK' hR' ⟨a, ha⟩ = B.mkQ (b : W) := by
    rw [← h]
    exact henc
  exact he.symm.trans
    ((encodeFixed_relation A A0 B B0 X' hK' hR' ⟨a, ha⟩ b).mp henc')

def Valid (A : Submodule K V) (B : Submodule K W)
    (p : LinearIdentities.A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ p.2.2.ker = B.comap p.2.1.subtype ∧
    p.2.2.range = A.map p.1.mkQ

abbrev Index (A : Submodule K V) (B : Submodule K W) :=
  {p : LinearIdentities.A4Index (K := K) (W := W) (V := V) // Valid A B p}

abbrev GeometricIndex (A : Submodule K V) (B : Submodule K W) := Index A B

def encode (A : Submodule K V) (B : Submodule K W)
    (p : Index A B) : A →ₗ[K] (W ⧸ B) :=
  encodeFixed A p.val.1 B p.val.2.1 p.val.2.2
    p.property.2.2.1 p.property.2.2.2

theorem encode_injective (A : Submodule K V) (B : Submodule K W) :
    Function.Injective (encode A B) := by
  rintro ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩ ⟨⟨A0', B0', X'⟩, hA', hB', hK', hR'⟩ h
  change encodeFixed A A0 B B0 X hK hR = encodeFixed A A0' B B0' X' hK' hR' at h
  have hAeq : A0 = A0' := by
    calc
      A0 = (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype :=
        (recover_A0 A A0 B B0 X hK hR hA).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').ker.map A.subtype :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.ker.map A.subtype) h
      _ = A0' := recover_A0 A A0' B B0' X' hK' hR' hA'
  have hBeq : B0 = B0' := by
    calc
      B0 = (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ :=
        (recover_B0 A A0 B B0 X hK hR hB).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').range.comap B.mkQ :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.range.comap B.mkQ) h
      _ = B0' := recover_B0 A A0' B B0' X' hK' hR' hB'
  cases hAeq
  cases hBeq
  have hXeq := encodeFixed_injective A A0 B B0 X X' hK hR hK' hR' h
  cases hXeq
  rfl

end Generic

open Integration.BinaryLinear

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_index_le (A : Submodule F2 V) (B : Submodule F2 W) :
    Nat.card (Index A B) ≤
      2 ^ (Module.finrank F2 A * Module.finrank F2 (W ⧸ B)) := by
  have hc := CompressionCount.natCard_linearMap (U := A) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode A B) (encode_injective A B)
  rwa [hc] at h

theorem card_geometricIndex_le (A : Submodule F2 V) (B : Submodule F2 W) :
    Nat.card (GeometricIndex A B) ≤
      2 ^ (Module.finrank F2 A * Module.finrank F2 (W ⧸ B)) := card_index_le A B

end DFVSGames.Appendix.A4IndexCount

end

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix.Derivatives

namespace DFVSGames.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

private theorem indicator_eq_sum_of_unique_inline_OperatorPartitions {I : Type*} [Fintype I]
    (P : Prop) (R : I → Prop) (a : ℝ)
    (hpart : P → ∃! i, R i) (hback : ∀ i, R i → P) :
    (if P then a else 0) = ∑ i, if R i then a else 0 := by
  classical
  by_cases hp : P
  · obtain ⟨i, hi, hu⟩ := hpart hp
    rw [ite_eq_left hp]
    symm
    calc
      (∑ j, if R j then a else 0) = if R i then a else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact ite_eq_right (fun hj => hji (hu j hj))
        · simp
      _ = a := ite_eq_left hi
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hp (hback i hi))

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem spectralProjector_partition {I : Type*} [Fintype I]
    (P : (F →ₗ[F2] E) → Prop) (R : I → (F →ₗ[F2] E) → Prop)
    (hpart : ∀ Y, P Y → ∃! i, R i Y)
    (hback : ∀ i Y, R i Y → P Y) (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P f = ∑ i, spectralProjector (R i) f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_spectralProjector, linearCoeff_sum]
  simp only [linearCoeff_spectralProjector]
  exact indicator_eq_sum_of_unique_inline_OperatorPartitions (P Y) (fun i => R i Y)
    (linearCoeff f Y) (hpart Y) (fun i => hback i Y)

variable [Finite E] [Finite F]

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (DFVSGames.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    DFVSGames.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open DFVSGames.Appendix.LinearIdentities
open DFVSGames.Appendix.RankAdditivity

abbrev A4Geometry (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Valid A B

abbrev A4GeometricIndex (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Index A B

def a4Mask (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2.1 ∧
    RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem a4Mask_unique (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (hY : A ≤ Y.range ∧ Y.ker ≤ B) :
    ∃! i : A4GeometricIndex A B, a4Mask A B i Y := by
  obtain ⟨p, hp, hu⟩ := (BinaryA4.a4_unique_selector Y A B).mp hY
  rcases hp with ⟨hA, hB, hinner, hker, hrange, hrank⟩
  let i : A4GeometricIndex A B := ⟨p, hA, hB, hker, hrange⟩
  refine ⟨i, ⟨hinner, hrank⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjA, hjB, hjker, hjrange⟩
  exact ⟨hjA, hjB, hj.1, hjker, hjrange, hj.2⟩

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
omit [FiniteDimensional F2 E] in
theorem a4Mask_implies_weak (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E)
    (hi : a4Mask A B i Y) : A ≤ Y.range ∧ Y.ker ≤ B := by
  rcases i.property with ⟨_, _, hker, hrange⟩
  exact a4_weak_selector_of_summand Y i.val.1 A B i.val.2.1 i.val.2.2
    hi.1 hker hrange hi.2

omit [Finite E] [Finite F] in
theorem a4_projector_partition (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f =
      ∑ i : A4GeometricIndex A B, spectralProjector (a4Mask A B i) f := by
  exact spectralProjector_partition _ _
    (a4Mask_unique A B) (a4Mask_implies_weak A B) f

def A5Geometry (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (p : Submodule F2 E × Submodule F2 F) : Prop :=
  Disjoint p.1 X.range ∧ p.1 ⊔ X.range = A ∧
    p.2 ⊔ X.ker = ⊤ ∧ p.2 ⊓ X.ker = B

abbrev A5GeometricIndex (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F) :=
  {p : Submodule F2 E × Submodule F2 F // A5Geometry X A B p}

def a5Mask (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2 ∧
    RankBelow (compress X i.val.1 i.val.2) (compress Y i.val.1 i.val.2)

def a5OuterMask (X : F →ₗ[F2] E) (A : Submodule F2 E)
    (B : Submodule F2 F) (Y : F →ₗ[F2] E) : Prop :=
  RankBelow X Y ∧ Hybrid (compress Y X.range X.ker)
    (A.map X.range.mkQ) (B.comap X.ker.subtype)

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
omit [FiniteDimensional F2 E] in
theorem a5Mask_unique (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (Y : F →ₗ[F2] E) (hY : a5OuterMask X A B Y) :
    ∃! i : A5GeometricIndex X A B, a5Mask X A B i Y := by
  obtain ⟨p, hp, hu⟩ := (a5_unique_selector X Y A B hI hB).mp hY
  rcases hp with ⟨hinner, hdis, hA, hcover, hmeet, hlocal⟩
  let i : A5GeometricIndex X A B := ⟨p, hdis, hA, hcover, hmeet⟩
  refine ⟨i, ⟨hinner, hlocal⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjdis, hjA, hjcover, hjmeet⟩
  exact ⟨hj.1, hjdis, hjA, hjcover, hjmeet, hj.2⟩

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
omit [FiniteDimensional F2 E] in
theorem a5Mask_implies_outer (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E)
    (hi : a5Mask X A B i Y) : a5OuterMask X A B Y := by
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  exact ⟨rankBelow_of_compressed_rankBelow X Y i.val.1 i.val.2
      hi.1 hdis hcover hi.2,
    reverse_outer_hybrid X Y i.val.1 A B i.val.2
      hi.1 hdis hA hcover hmeet hi.2⟩

omit [Finite E] [Finite F] in
theorem a5_projector_partition (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (a5OuterMask X A B) f =
      ∑ i : A5GeometricIndex X A B, spectralProjector (a5Mask X A B i) f := by
  exact spectralProjector_partition _ _
    (a5Mask_unique X A B hI hB) (a5Mask_implies_outer X A B) f

end DFVSGames.Appendix.OperatorPartitions
end

noncomputable section

namespace DFVSGames.Appendix.RestrictionTransport

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def nestedEmbedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D →ₗ[F2] (E →ₗ[F2] F) :=
  (embedding A B).comp (embedding C D)

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  constructor
  · rintro ⟨N, rfl⟩
    constructor
    · intro x hx
      change (embed C D N (A.mkQ x) : F) = 0
      have hz : embed C D N (A.mkQ x) = 0 := embed_vanishes C D N hx
      rw [hz]
      rfl
    · rintro y ⟨x, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨embed C D N (A.mkQ x), ?_, rfl⟩
      exact embed_range C D N ⟨A.mkQ x, rfl⟩
  · rintro ⟨hker, hrange⟩
    have hA : A ≤ M.ker := by
      intro x hx
      apply hker
      change A.mkQ x ∈ C
      have hz : A.mkQ x = 0 := by simpa using hx
      rw [hz]
      exact C.zero_mem
    have hB : M.range ≤ B := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hrange hy)
      exact b.property
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr ⟨hA, hB⟩
    have hC : C ≤ N.ker := by
      intro q hq
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      change N (A.mkQ x) = 0
      apply Subtype.ext
      change embed A B N x = 0
      rw [hN]
      exact hker hq
    have hD : N.range ≤ D := by
      rintro b ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      have hm : M x ∈ D.map B.subtype := hrange ⟨x, rfl⟩
      have hco : (N (A.mkQ x) : F) = M x := congrArg (fun L : E →ₗ[F2] F => L x) hN
      rw [← hco] at hm
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hm
      have heq' : b = N (A.mkQ x) := Subtype.ext heq
      exact heq' ▸ hb
    obtain ⟨P, hP⟩ := (exists_embed_iff C D N).mpr ⟨hC, hD⟩
    refine ⟨P, ?_⟩
    change embed A B (embed C D P) = M
    rw [hP, hN]

theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Nested

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

private theorem exists_range_preimage_inline_RestrictionTransport (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (h : f.range ≤ g.range) (x : P) : ∃ y : Q, g y = f x := h ⟨x, rfl⟩

def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q := by
  let fw (x : P) := Classical.choose (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  let bw (y : Q) := Classical.choose (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  have hfw (x : P) : g (fw x) = f x :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  have hbw (y : Q) : f (bw y) = g y :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  exact
    { toFun := fw
      invFun := bw
      left_inv := by
        intro x
        apply hf
        rw [hbw, hfw]
      right_inv := by
        intro y
        apply hg
        rw [hfw, hbw]
      map_add' := by
        intro x y
        apply hg
        simp only [map_add, hfw]
      map_smul' := by
        intro c x
        change fw (c • x) = c • fw x
        apply hg
        simp only [map_smul, hfw] }

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

theorem restriction_secondMoment_eq_of_same_range
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) (T : G) :
    (𝔼 x, observable (T + f x) ^ 2) = 𝔼 y, observable (T + g y) ^ 2 :=
  expect_eq_of_same_range f g hf hg h (fun z => observable (T + z) ^ 2)

theorem restriction_energySquare_average_eq_of_same_range [Fintype G]
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 T, (𝔼 x, observable (T + f x) ^ 2) ^ 2) =
      𝔼 T, (𝔼 y, observable (T + g y) ^ 2) ^ 2 := by
  apply Finset.expect_congr rfl
  intro T _
  rw [restriction_secondMoment_eq_of_same_range f g hf hg h observable T]

end SameRange

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

local instance nestedMomentsQuotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

theorem nested_restriction_secondMoment_eq
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (h : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    (𝔼 N, h (T + nestedEmbedding A B C D N) ^ 2) =
      𝔼 M, h (T + embed (C.comap A.mkQ) (D.map B.subtype) M) ^ 2 := by
  have transport := restriction_secondMoment_eq_of_same_range
    (K := F2) (P := Parameter C D)
    (Q := Parameter (C.comap A.mkQ) (D.map B.subtype))
    (G := E →ₗ[F2] F)
    (nestedEmbedding A B C D) (embedding (C.comap A.mkQ) (D.map B.subtype))
    (nestedEmbedding_injective A B C D)
    (embed_injective (C.comap A.mkQ) (D.map B.subtype))
    (nested_range_eq A B C D) h T
  exact transport

theorem nested_restriction_energySquare_average_eq [Fintype (E →ₗ[F2] F)]
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (h : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, (𝔼 N, h (T + nestedEmbedding A B C D N) ^ 2) ^ 2) =
      𝔼 T, (𝔼 M, h (T + embed (C.comap A.mkQ) (D.map B.subtype) M) ^ 2) ^ 2 := by
  apply Finset.expect_congr rfl
  intro T _
  rw [nested_restriction_secondMoment_eq A B C D h T]

end DFVSGames.Appendix.RestrictionTransport

namespace DFVSGames.Appendix.LinearIdentities

variable {K : Type*} {W : Type*} {V : Type*} [Field K]
  [AddCommGroup W] [AddCommGroup V] [Module K W] [Module K V]

theorem a5_preimage_eq_ker (X : W →ₗ[K] V) (A₀ : Submodule K V)
    (hd : Disjoint A₀ (LinearMap.range X)) : A₀.comap X = LinearMap.ker X := by
  ext w
  constructor
  · intro hw
    exact Submodule.disjoint_def.mp hd (X w) hw ⟨w, rfl⟩
  · intro hw
    change X w ∈ A₀
    rw [show X w = 0 from hw]
    exact A₀.zero_mem

theorem a5_range_domRestrict_eq_of_cover (X : W →ₗ[K] V) (B₀ : Submodule K W)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    LinearMap.range (X.domRestrict B₀) = LinearMap.range X := by
  apply le_antisymm (LinearMap.range_domRestrict_le_range X B₀)
  rintro v ⟨w, hw⟩
  have ht : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp ht with ⟨b, hb, k, hk, hbk⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change X b = v
  rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]

theorem a5_effective_annihilator (X : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    (LinearMap.range (compress X A₀ B₀)).comap A₀.mkQ = A := by
  rw [compress, LinearMap.range_comp, a5_range_domRestrict_eq_of_cover X B₀ hc,
    Submodule.comap_map_mkQ, hA]

theorem a5_effective_codomain (X : W →ₗ[K] V)
    (A₀ : Submodule K V) (B B₀ : Submodule K W)
    (hd : Disjoint A₀ (LinearMap.range X))
    (hB : B₀ ⊓ LinearMap.ker X = B) :
    (LinearMap.ker (compress X A₀ B₀)).map B₀.subtype = B := by
  rw [compress, LinearMap.ker_comp, Submodule.ker_mkQ]
  change ((A₀.comap X).comap B₀.subtype).map B₀.subtype = B
  rw [a5_preimage_eq_ker X A₀ hd, Submodule.map_comap_subtype, hB]

end DFVSGames.Appendix.LinearIdentities
end

noncomputable section
namespace DFVSGames.Appendix.HybridComposition

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives DFVSGames.Appendix.LinearIdentities
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem effective_hybrid_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (Y : F →ₗ[F2] E) :
    (Hybrid Y A B ∧ Hybrid (Restriction.compressFrequency A B Y) C D) ↔
      Hybrid Y (C.comap A.mkQ) (D.map B.subtype) := by
  have hA : A ≤ C.comap A.mkQ := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map B.subtype ≤ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hC : (C.comap A.mkQ).map A.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := A.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hD : (D.map B.subtype).comap B.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hh := LinearIdentities.nested_hybrid_iff Y A (C.comap A.mkQ)
    (D.map B.subtype) B hA hB
  rw [hC, hD] at hh
  have hc : Restriction.compressFrequency A B Y = LinearIdentities.compress Y A B := by
    ext x
    rfl
  simpa only [hc] using hh

theorem nested_hybridDerivative_energy
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B) :
    (𝔼 N, hybridDerivative C D S (hybridDerivative A B T f) N ^ 2) =
      𝔼 M, hybridDerivative (C.comap A.mkQ) (D.map B.subtype)
        (T + embed A B S) f M ^ 2 := by
  let g := hybridProjector (C.comap A.mkQ) (D.map B.subtype) f
  have hp : (fun Y => Hybrid Y A B ∧
        Hybrid (Restriction.compressFrequency A B Y) C D) =
      (fun Y => Hybrid Y (C.comap A.mkQ) (D.map B.subtype)) := by
    funext Y
    exact propext (effective_hybrid_iff A B C D Y)
  have hh := OperatorPartitions.spectralProjector_restriction_projector A B
    (fun Y => Hybrid Y A B) (fun Z => Hybrid Z C D) f T
  rw [hp] at hh
  have hval (N : Parameter C D) :
      hybridDerivative C D S (hybridDerivative A B T f) N =
      g ((T + embed A B S) + RestrictionTransport.nestedEmbedding A B C D N) := by
    change restrict (spectralProjector (fun Z => Hybrid Z C D)
      (restrict (spectralProjector (fun Y => Hybrid Y A B) f) A B T)) C D S N = _
    rw [hh]
    change g (T + (embedding A B) (S + embed C D N)) =
      g ((T + (embedding A B) S) + (embedding A B) (embed C D N))
    rw [map_add, add_assoc]
  simp_rw [hval]
  exact RestrictionTransport.nested_restriction_secondMoment_eq A B C D g
    (T + embed A B S)

theorem nested_hybridDerivative_energySquare_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 S, (𝔼 N,
      hybridDerivative C D S (hybridDerivative A B T f) N ^ 2)^2) =
    𝔼 U, (𝔼 M, hybridDerivative (C.comap A.mkQ) (D.map B.subtype) U f M ^ 2)^2 := by
  simp_rw [nested_hybridDerivative_energy A B C D f]
  exact Restriction.real_translation_average (embed A B)
    (fun U => (𝔼 M,
      hybridDerivative (C.comap A.mkQ) (D.map B.subtype) U f M ^ 2)^2)

omit [Finite E] in
theorem finrank_comap_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) :
    Module.finrank F2 (C.comap A.mkQ) = Module.finrank F2 A + Module.finrank F2 C := by
  let P := C.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  let q : P →ₗ[F2] (E ⧸ A) := A.mkQ.comp P.subtype
  have hR : q.range = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y, hy⟩ := A.mkQ_surjective x
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change A.mkQ y ∈ C
        rw [hy]
        exact hx
      · exact hy
  have hK : q.ker.map P.subtype = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hz : (y : E) ∈ LinearMap.ker A.mkQ := hy
      change (y : E) ∈ A
      simpa only [Submodule.ker_mkQ] using hz
    · intro hx
      refine Submodule.mem_map.mpr ⟨⟨x, hAP hx⟩, ?_, rfl⟩
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
  have hKdim := Submodule.finrank_map_subtype_eq P q.ker
  rw [hK] at hKdim
  have hdim := q.finrank_range_add_finrank_ker
  rw [hR, ← hKdim] at hdim
  change Module.finrank F2 P = Module.finrank F2 A + Module.finrank F2 C
  omega

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite F] in
omit [Finite E] in
theorem order_effective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    order (C.comap A.mkQ) (D.map B.subtype) = order A B + order C D := by
  have hA := finrank_comap_mkQ A C
  have hD := Submodule.finrank_map_subtype_eq B D
  have hFB := B.finrank_quotient_add_finrank
  have hBD := D.finrank_quotient_add_finrank
  have hFbar := (D.map B.subtype).finrank_quotient_add_finrank
  change Module.finrank F2 (C.comap A.mkQ) +
      Module.finrank F2 (F ⧸ D.map B.subtype) =
    (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      (Module.finrank F2 C + Module.finrank F2 (B ⧸ D))
  omega

end DFVSGames.Appendix.HybridComposition
end

end OAI

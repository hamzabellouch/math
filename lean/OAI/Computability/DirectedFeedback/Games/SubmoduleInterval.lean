import Mathlib
import OAI.Computability.DirectedFeedback.Games.A5Scalar

namespace OAI

namespace DFVSGames.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalEquiv (I : Submodule 𝕜 V) :
    {A : Submodule 𝕜 V // A ≤ I} ≃ Submodule 𝕜 I where
  toFun A := A.val.comap I.subtype
  invFun B := ⟨B.map I.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact b.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.comap I.subtype).map I.subtype = A.val
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact Submodule.mem_map.mpr ⟨⟨x, A.property hx⟩, hx, rfl⟩
  right_inv B := by
    change (B.map I.subtype).comap I.subtype = B
    ext b
    constructor
    · intro hb
      change (b : V) ∈ B.map I.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨c, hc, hcb⟩
      have h : c = b := Subtype.ext hcb
      simpa only [h] using hc
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩

def lowerIntervalSpaceEquiv (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    A.val ≃ₗ[𝕜] A.val.comap I.subtype where
  toFun a := ⟨⟨a.val, A.property a.property⟩, a.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _a := Subtype.ext rfl
  right_inv _b := Subtype.ext (Subtype.ext rfl)
  map_add' _a _b := Subtype.ext (Subtype.ext rfl)
  map_smul' _c _a := Subtype.ext (Subtype.ext rfl)

theorem lowerInterval_finrank (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    finrank 𝕜 (lowerIntervalEquiv I A) = finrank 𝕜 A.val :=
  (lowerIntervalSpaceEquiv I A).finrank_eq.symm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_lowerInterval {R : Type*} [AddCommMonoid R]
    (I : Submodule 𝕜 V) [Fintype {A : Submodule 𝕜 V // A ≤ I}]
    [Fintype (Submodule 𝕜 I)] (weight : Nat → R) :
    (∑ A : {A : Submodule 𝕜 V // A ≤ I}, weight (finrank 𝕜 A.val)) =
      ∑ B : Submodule 𝕜 I, weight (finrank 𝕜 B) := by
  apply Fintype.sum_equiv (lowerIntervalEquiv I)
  intro A
  rw [lowerInterval_finrank]

local instance submoduleFinite [Finite V] : Finite (Submodule 𝕜 V) :=
  Finite.of_injective (fun S : Submodule 𝕜 V => (S : Set V)) SetLike.coe_injective

noncomputable def lowerWeightedTotal [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  exact ∑ A : {A : Submodule 𝕜 V // A ≤ I}, w (finrank 𝕜 A.val)

theorem lowerWeightedTotal_eq [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) :
    lowerWeightedTotal I w = SubspaceExtensions.weightedTotal (K := 𝕜) (V := I) w := by
  classical
  let := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  let := SubspaceExtensions.subspaceFintype (K := 𝕜) (V := I)
  unfold lowerWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (lowerIntervalEquiv I)
    (fun A : {A : Submodule 𝕜 V // A ≤ I} => w (finrank 𝕜 A.val))
    (fun B : Submodule 𝕜 I => w (finrank 𝕜 B))
    (fun A => congrArg w (lowerInterval_finrank I A).symm)

theorem binary_lower_interval_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] (I : Submodule (ZMod 2) E) :
    lowerWeightedTotal I (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if I = ⊥ then 1 else 0 := by
  rw [lowerWeightedTotal_eq, SubspaceExtensions.binary_subspace_mobius]
  simp only [Submodule.finrank_eq_zero]

end DFVSGames.Appendix.SubmoduleInterval

noncomputable section

namespace DFVSGames.Appendix.A13Index

open Module
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixRestrictions (order)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev Triple := LinearIdentities.A4Index (K := F2) (W := F) (V := E)

def weakA (q : Triple (E := E) (F := F)) : Submodule F2 E :=
  q.2.2.range.comap q.1.mkQ

def weakB (q : Triple (E := E) (F := F)) : Submodule F2 F :=
  q.2.2.ker.map q.2.1.subtype

theorem recover_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakA p.val = A := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.range.comap A0.mkQ = A
  rw [hR]
  ext a
  change A0.mkQ a ∈ A.map A0.mkQ ↔ a ∈ A
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨v, hv, he⟩
    have hm : a - v ∈ A0 := by
      apply (Submodule.Quotient.mk_eq_zero A0).mp
      change A0.mkQ (a - v) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using A.add_mem (hA hm) hv
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

theorem recover_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakB p.val = B := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.ker.map B0.subtype = B
  rw [hK]
  ext b
  constructor
  · intro hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem canonicalValid (q : Triple (E := E) (F := F)) :
    A4IndexCount.Valid (weakA q) (weakB q) q := by
  rcases q with ⟨A0, B0, X⟩
  change A0 ≤ X.range.comap A0.mkQ ∧ X.ker.map B0.subtype ≤ B0 ∧
    X.ker = (X.ker.map B0.subtype).comap B0.subtype ∧
    X.range = (X.range.comap A0.mkQ).map A0.mkQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change A0.mkQ a ∈ X.range
    have hz : A0.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero A0).mpr ha
    rw [hz]
    exact X.range.zero_mem
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact v.property
  · ext b
    constructor
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro hb
      change (b : F) ∈ X.ker.map B0.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨v, hv, he⟩
      have h : v = b := Subtype.ext he
      simpa only [h] using hv
  · ext z
    constructor
    · intro hz
      obtain ⟨v, rfl⟩ := A0.mkQ_surjective z
      exact Submodule.mem_map.mpr ⟨v, hz, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hv

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem dim_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 A = finrank F2 p.val.1 + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 A = finrank F2 A0 + finrank F2 X.range
  let Q := A4IndexCount.quotientRestriction A0 A
  have hQR : Q.range = X.range := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, he⟩
  have hQK : finrank F2 Q.ker = finrank F2 A0 := by
    rw [A4IndexCount.ker_quotientRestriction]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv A ⟨A0, hA⟩).finrank_eq.symm
  have h := Q.finrank_range_add_finrank_ker
  rw [hQR, hQK] at h
  omega

omit [FiniteDimensional F2 E] in
theorem codim_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 (F ⧸ B) =
      finrank F2 (F ⧸ p.val.2.1) + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 (F ⧸ B) = finrank F2 (F ⧸ B0) + finrank F2 X.range
  have hKB : finrank F2 X.ker = finrank F2 B := by
    rw [hK]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv B0 ⟨B, hB⟩).finrank_eq.symm
  have h := X.finrank_range_add_finrank_ker
  rw [hKB] at h
  have hBdim := B.finrank_quotient_add_finrank
  have hB0dim := B0.finrank_quotient_add_finrank
  omega

def size (q : Triple (E := E) (F := F)) : Nat :=
  order q.1 q.2.1 + finrank F2 q.2.2.range

theorem weak_order {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    order A B = order p.val.1 p.val.2.1 + 2 * finrank F2 p.val.2.2.range := by
  have ha := dim_weakA p
  have hb := codim_weakB p
  dsimp only [order]
  omega

theorem order_eq_zero_iff (A : Submodule F2 E) (B : Submodule F2 F) :
    order A B = 0 ↔ A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    change finrank F2 A + finrank F2 (F ⧸ B) = 0 at h
    have ha : finrank F2 A = 0 := by omega
    have hb : finrank F2 (F ⧸ B) = 0 := by omega
    refine ⟨Submodule.finrank_eq_zero.mp ha, ?_⟩
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hq := B.finrank_quotient_add_finrank
    omega
  · rintro ⟨rfl, rfl⟩
    simpa [order] using
      (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem valid_positive_iff {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    (A, B) ≠ (⊥, ⊤) ↔ 0 < size p.val := by
  have h := weak_order p
  constructor
  · intro hp
    by_contra ht
    have hz : order A B = 0 := by
      dsimp only [size] at ht
      omega
    rcases (order_eq_zero_iff A B).mp hz with ⟨hA, hB⟩
    exact hp (Prod.ext hA hB)
  · intro ht hp
    have hAB : A = ⊥ ∧ B = ⊤ := Prod.mk.inj hp
    have hz := (order_eq_zero_iff A B).mpr hAB
    dsimp only [size] at ht
    omega

abbrev WeakPositive :=
  {p : Submodule F2 E × Submodule F2 F // p ≠ (⊥, ⊤)}

abbrev PositiveWitness :=
  Σ p : WeakPositive (E := E) (F := F), A4IndexCount.Index p.val.1 p.val.2

abbrev PositiveTriple := {q : Triple (E := E) (F := F) // 0 < size q}

abbrev BoundedPositiveTriple (d : Nat) :=
  {q : Triple (E := E) (F := F) // 0 < size q ∧ size q ≤ d}

def positiveMap (p : PositiveWitness (E := E) (F := F)) :
    PositiveTriple (E := E) (F := F) :=
  ⟨p.2.val, (valid_positive_iff p.2).mp p.1.property⟩

theorem positiveMap_injective :
    Function.Injective (positiveMap (E := E) (F := F)) := by
  rintro ⟨⟨⟨A, B⟩, hp⟩, p⟩ ⟨⟨⟨A', B'⟩, hp'⟩, p'⟩ he
  have hraw : p.val = p'.val := congrArg Subtype.val he
  have hA : A = A' := by
    calc
      A = weakA p.val := (recover_weakA p).symm
      _ = weakA p'.val := congrArg weakA hraw
      _ = A' := recover_weakA p'
  have hB : B = B' := by
    calc
      B = weakB p.val := (recover_weakB p).symm
      _ = weakB p'.val := congrArg weakB hraw
      _ = B' := recover_weakB p'
  cases hA
  cases hB
  have hpp : p = p' := Subtype.ext hraw
  cases hpp
  rfl

def positiveInverse (q : PositiveTriple (E := E) (F := F)) :
    PositiveWitness (E := E) (F := F) :=
  ⟨⟨(weakA q.val, weakB q.val),
      (valid_positive_iff ⟨q.val, canonicalValid q.val⟩).mpr q.property⟩,
    ⟨q.val, canonicalValid q.val⟩⟩

def positiveEquiv : PositiveWitness (E := E) (F := F) ≃
    PositiveTriple (E := E) (F := F) :=
  Equiv.ofBijective positiveMap ⟨positiveMap_injective, by
    intro q
    refine ⟨positiveInverse q, ?_⟩
    exact Subtype.ext rfl⟩

@[simp] theorem positiveMap_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveMap p).val = p.2.val := rfl

@[simp] theorem positiveEquiv_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveEquiv p).val = p.2.val := rfl

@[instance_reducible]
def tripleFintype [Finite E] [Finite F] :
    Fintype (Triple (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  letI (A : Submodule F2 E) : Finite (E ⧸ A) :=
    Finite.of_surjective A.mkQ A.mkQ_surjective
  letI (A : Submodule F2 E) (B : Submodule F2 F) :
      Fintype (B →ₗ[F2] (E ⧸ A)) := by
    letI : Fintype B := Fintype.ofFinite _
    letI : Fintype (E ⧸ A) := Fintype.ofFinite _
    exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) =>
      (L : B → E ⧸ A)) DFunLike.coe_injective
  exact inferInstance

@[instance_reducible]
def weakPositiveFintype [Finite E] [Finite F] :
    Fintype (WeakPositive (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  exact inferInstance

@[instance_reducible]
def geometricIndexFintype [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (A4IndexCount.Index A B) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def positiveWitnessFintype [Finite E] [Finite F] :
    Fintype (PositiveWitness (E := E) (F := F)) := by
  classical
  letI := weakPositiveFintype (E := E) (F := F)
  letI (A : Submodule F2 E) (B : Submodule F2 F) := geometricIndexFintype A B
  exact inferInstance

@[instance_reducible]
def positiveTripleFintype [Finite E] [Finite F] :
    Fintype (PositiveTriple (E := E) (F := F)) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def boundedPositiveTripleFintype [Finite E] [Finite F] (d : Nat) :
    Fintype (BoundedPositiveTriple (E := E) (F := F) d) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

end DFVSGames.Appendix.A13Index
end

namespace DFVSGames.Appendix.TotalPredecessorCount
open Module
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

noncomputable def predecessorEnd (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) : Y.range →ₗ[F2] Y.range :=
  let R' : E →ₗ[F2] Y.range := R.val.codRestrict Y.range
    (fun x => range_le_of_rankBelow R.val Y R.property ⟨x,rfl⟩)
  let hker : Y.ker ≤ R'.ker := by
    intro x hx
    exact Subtype.ext (ker_le_of_rankBelow R.val Y R.property hx)
  (Y.ker.liftQ R' hker).comp Y.quotKerEquivRange.symm.toLinearMap

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_recovery (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) (x : E) :
    ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) = R.val x := by
  have hq : Y.quotKerEquivRange.symm (Y.rangeRestrict x) = Y.ker.mkQ x :=
    Y.quotKerEquivRange.symm_apply_apply (Y.ker.mkQ x)
  dsimp only [predecessorEnd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hq]
  rfl

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_injective (Y : E →ₗ[F2] F) :
    Function.Injective (predecessorEnd Y) := by
  intro R S h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  calc
    R.val x = ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) :=
      (predecessorEnd_recovery Y R x).symm
    _ = ((predecessorEnd Y S (Y.rangeRestrict x) : Y.range) : F) :=
      congrArg (fun P : Y.range →ₗ[F2] Y.range => (P (Y.rangeRestrict x) : F)) h
    _ = S.val x := predecessorEnd_recovery Y S x

omit [FiniteDimensional F2 F] in
theorem card_predecessors_le [Finite E] [Finite F] (Y : E →ₗ[F2] F) :
    Nat.card {R : E →ₗ[F2] F // RankBelow R Y} ≤
      2 ^ (finrank F2 Y.range ^ 2) := by
  classical
  let : Finite (Y.range →ₗ[F2] Y.range) :=
    Finite.of_injective (fun f : Y.range →ₗ[F2] Y.range => (f : Y.range → Y.range))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective (predecessorEnd Y)
    (predecessorEnd_injective Y)
  rw [CompressionCount.natCard_linearMap] at h
  simpa only [pow_two] using h
end DFVSGames.Appendix.TotalPredecessorCount

noncomputable section

namespace DFVSGames.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem linearTraceCharacter_re_add (S T : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter (S + T) X).re =
      (linearTraceCharacter S X).re * (linearTraceCharacter T X).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply]
  rw [← linearTraceCharacter_real S X, ← linearTraceCharacter_real T X]
  simp

variable [Fintype (E →ₗ[F2] F)]

theorem linearCoeff_mul_character (f : (E →ₗ[F2] F) → ℝ)
    (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * (linearTraceCharacter T X).re) S =
      linearCoeff f (S + T) := by
  simp only [linearCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [linearTraceCharacter_re_add]
  ac_rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_mul (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * g X) S =
      ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T) := by
  have hexpand : (fun X : E →ₗ[F2] F => f X * g X) =
      ∑ T : F →ₗ[F2] E, linearCoeff f T •
        (fun X => g X * (linearTraceCharacter T X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      f X * g X =
          (∑ T : F →ₗ[F2] E, linearCoeff f T * (linearTraceCharacter T X).re) * g X := by
        rw [linear_fourier_inversion]
      _ = ∑ T : F →ₗ[F2] E,
          linearCoeff f T * (g X * (linearTraceCharacter T X).re) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ac_rfl
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_mul_character]

def coefficientConvolution (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T)

theorem expect_fourth_eq_sum_convolution_sq (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X ^ 4) =
      ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
  calc
    (𝔼 X, f X ^ 4) = 𝔼 X, (f X * f X) ^ 2 := by
      apply Finset.expect_congr rfl
      intro X _
      rw [← pow_two, ← pow_mul]
    _ = ∑ S : F →ₗ[F2] E, linearCoeff (fun X => f X * f X) S ^ 2 :=
      (linear_parseval (fun X => f X * f X)).symm
    _ = ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
      simp only [linearCoeff_mul, coefficientConvolution]

end DFVSGames.Fourier.MatrixProducts
end

noncomputable section
namespace DFVSGames.Appendix.F1Energy
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

def rank (Y : G) : ℕ := Module.finrank F2 Y.range

def Good (X Y : G) : Prop :=
  ∃ R : G, RankBelow R X ∧ RankBelow R Y ∧ RankBelow (X + R) (X + Y)

abbrev BoundedSplit (d : ℕ) (X : G) :=
  {R : G // RankBelow R X ∧ rank R ≤ d ∧ rank (X + R) ≤ d}

theorem add_self_cancel (X R : G) : (X + R) + R = X := by
  rw [add_assoc, DegreeCover.binary_add_self, add_zero]

def translate (R : G) : G ≃ G where
  toFun X := X + R
  invFun X := X + R
  left_inv X := add_self_cancel X R
  right_inv X := add_self_cancel X R

theorem rank_le_of_rankBelow {R Y : G} (h : RankBelow R Y) : rank R ≤ rank Y := by
  change rank Y = rank R + rank (Y - R) at h
  omega

theorem boundedSplit_rank (d : ℕ) (X : G) (R : BoundedSplit d X) : rank X ≤ 2*d := by
  have h := R.property.1
  change rank X = rank R.val + rank (X - R.val) at h
  simp only [sub_eq_add_neg, DegreeCover.binary_neg] at h
  have hR := R.property.2.1
  have hS := R.property.2.2
  omega

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in

theorem good_of_trivial_intersections (X Y : G)
    (hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥)
    (hk : X.ker ⊔ Y.ker ⊔ (X+Y).ker = ⊤) : Good X Y := by
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  obtain ⟨R,S,C,hX,hY,hZ,hrX,hrY,hrZ⟩ :=
    DegreeCover.outside_bad_rank_cover Y (X+Y)
      (by simpa only [hc] using hi) (by simpa only [hc] using hk)
  have hXS : X = R+S := hc.symm.trans hX
  have hXR : X-R = S := by rw [hXS]; abel
  have hYR : Y-R = C := by rw [hY]; abel
  have hZS : (X+Y)-S = C := by rw [hZ]; abel
  have hSR : X+R = S := by simpa only [sub_eq_add_neg, DegreeCover.binary_neg] using hXR
  change rank (Y+(X+Y)) = rank R + rank S at hrX
  rw [hc] at hrX
  change rank Y = rank R + rank C at hrY
  change rank (X+Y) = rank S + rank C at hrZ
  refine ⟨R, ?_, ?_, ?_⟩
  · change rank X = rank R + rank (X-R)
    rw [hXR]
    exact hrX
  · change rank Y = rank R + rank (Y-R)
    rw [hYR]
    exact hrY
  · rw [hSR]
    change rank (X+Y) = rank S + rank ((X+Y)-S)
    rw [hZS]
    exact hrZ

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem sum_translate (R : G) (f : G → ℝ) :
    (∑ X, f (X+R)) = ∑ X, f X := Equiv.sum_comp (translate R) f

omit [FiniteDimensional F2 F] in
theorem card_bounded_splits_le (d : ℕ) (X : G) :
    Nat.card (BoundedSplit d X) ≤ 2^(4*d^2) := by
  classical
  by_cases h : Nonempty (BoundedSplit d X)
  · have hr := boundedSplit_rank d X (Classical.choice h)
    let inc : BoundedSplit d X → {R : G // RankBelow R X} :=
      fun R => ⟨R.val, R.property.1⟩
    have hinj : Function.Injective inc := by
      intro R S hRS
      exact Subtype.ext (congrArg (fun T : {R : G // RankBelow R X} => T.val) hRS)
    have hc := Nat.card_le_card_of_injective inc hinj
    have hp := TotalPredecessorCount.card_predecessors_le X
    change Nat.card {R : G // RankBelow R X} ≤ 2^(rank X^2) at hp
    have hs : rank X^2 ≤ 4*d^2 := by nlinarith
    exact hc.trans (hp.trans (Nat.pow_le_pow_right (by decide) hs))
  · have hz : Fintype.card (BoundedSplit d X) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun R => h ⟨R⟩⟩
    simp only [Nat.card_eq_fintype_card, hz, zero_le]

omit [FiniteDimensional F2 F] in
theorem card_predecessors_cast_le (d : ℕ) (Y : G) (hy : rank Y ≤ d) :
    (Fintype.card {R : G // RankBelow R Y} : ℝ) ≤ (2:ℝ)^(d^2) := by
  have h := TotalPredecessorCount.card_predecessors_le Y
  change Nat.card {R : G // RankBelow R Y} ≤ 2^(rank Y^2) at h
  have hs : rank Y^2 ≤ d^2 := by nlinarith
  have hp := h.trans (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.card_eq_fintype_card] at hp
  exact_mod_cast hp

def predecessorCoefficient (a : G → ℝ) (R C : G) : ℝ :=
  if RankBelow R (R+C) then |a (R+C)| else 0

def gram (a : G → ℝ) (R S : G) : ℝ :=
  ∑ C, predecessorCoefficient a R C * predecessorCoefficient a S C

def predecessorEnergy (a : G → ℝ) : ℝ :=
  ∑ R, ∑ C, predecessorCoefficient a R C ^ 2

def goodConvolution (a : G → ℝ) (X : G) : ℝ :=
  ∑ Y, if Good X Y then |a Y| * |a (X+Y)| else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_nonneg (a : G → ℝ) (R C : G) :
    0 ≤ predecessorCoefficient a R C := by
  unfold predecessorCoefficient
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem gram_nonneg (a : G → ℝ) (R S : G) : 0 ≤ gram a R S :=
  Finset.sum_nonneg (fun C _ => mul_nonneg
    (predecessorCoefficient_nonneg a R C) (predecessorCoefficient_nonneg a S C))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_sq (a : G → ℝ) (R C : G) :
    predecessorCoefficient a R C ^ 2 =
      if RankBelow R (R+C) then a (R+C)^2 else 0 := by
  unfold predecessorCoefficient
  split <;> simp only [sq_abs, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_eq (a : G → ℝ) :
    predecessorEnergy a =
      ∑ Y, (Fintype.card {R : G // RankBelow R Y} : ℝ) * a Y^2 := by
  unfold predecessorEnergy
  calc
    _ = ∑ R, ∑ Y, if RankBelow R Y then a Y^2 else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [predecessorCoefficient_sq]
      simpa only [add_comm] using
        sum_translate R (fun Y => if RankBelow R Y then a Y^2 else 0)
    _ = ∑ Y, ∑ R, if RankBelow R Y then a Y^2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← F1Gram.sum_subtype_eq (fun R => RankBelow R Y) (fun _ => a Y^2)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_nonneg (a : G → ℝ) : 0 ≤ predecessorEnergy a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 F] in
theorem predecessor_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    predecessorEnergy a ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by
  rw [predecessor_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : rank Y ≤ d
  · exact mul_le_mul_of_nonneg_right (card_predecessors_cast_le d Y hY) (sq_nonneg _)
  · rw [hdegree Y (Nat.lt_of_not_ge hY)]
    simp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_nonneg (a : G → ℝ) (X : G) : 0 ≤ goodConvolution a X := by
  apply Finset.sum_nonneg
  intro Y _
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem good_term_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X Y : G) :
    (if Good X Y then |a Y| * |a (X+Y)| else 0) ≤
      ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) := by
  have hnonneg : 0 ≤ ∑ R : BoundedSplit d X,
      predecessorCoefficient a R.val (Y+R.val) *
        predecessorCoefficient a (X+R.val) (Y+R.val) :=
    Finset.sum_nonneg (fun R _ => mul_nonneg
      (predecessorCoefficient_nonneg a _ _) (predecessorCoefficient_nonneg a _ _))
  by_cases hg : Good X Y
  · rw [ite_eq_left hg]
    by_cases ha : a Y = 0
    · simpa only [ha, abs_zero, zero_mul] using hnonneg
    by_cases hb : a (X+Y) = 0
    · simpa only [hb, abs_zero, mul_zero] using hnonneg
    have hY : rank Y ≤ d := by
      by_contra hn
      exact ha (hdegree Y (Nat.lt_of_not_ge hn))
    have hZ : rank (X+Y) ≤ d := by
      by_contra hn
      exact hb (hdegree (X+Y) (Nat.lt_of_not_ge hn))
    obtain ⟨R,hRX,hRY,hSZ⟩ := hg
    let r : BoundedSplit d X := ⟨R,hRX,
      (rank_le_of_rankBelow hRY).trans hY, (rank_le_of_rankBelow hSZ).trans hZ⟩
    have h1 : R+(Y+R) = Y := by
      calc
        _ = (Y+R)+R := by abel
        _ = Y := add_self_cancel Y R
    have h2 : (X+R)+(Y+R) = X+Y := by
      calc
        _ = (X+Y)+(R+R) := by abel
        _ = X+Y := by rw [DegreeCover.binary_add_self, add_zero]
    have heq : predecessorCoefficient a r.val (Y+r.val) *
        predecessorCoefficient a (X+r.val) (Y+r.val) = |a Y| * |a (X+Y)| := by
      change predecessorCoefficient a R (Y+R) *
        predecessorCoefficient a (X+R) (Y+R) = _
      simp only [predecessorCoefficient, h1, h2, ite_eq_left hRY, ite_eq_left hSZ]
    rw [← heq]
    exact Finset.single_le_sum (fun (s : BoundedSplit d X) _ => mul_nonneg
      (predecessorCoefficient_nonneg a s.val (Y+s.val))
      (predecessorCoefficient_nonneg a (X+s.val) (Y+s.val)))
      (Finset.mem_univ r)
  · rw [ite_eq_right hg]
    exact hnonneg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_le_gram (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) := by
  calc
    _ ≤ ∑ Y, ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) :=
      Finset.sum_le_sum (fun Y _ => good_term_le a d hdegree X Y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R.val (fun C =>
        predecessorCoefficient a R.val C * predecessorCoefficient a (X+R.val) C)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_sq_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ^ 2 ≤ (2:ℝ)^(4*d^2) *
      ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
  have hg := goodConvolution_le_gram a d hdegree X
  have hn := goodConvolution_nonneg a X
  have hs : 0 ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) :=
    Finset.sum_nonneg (fun _ _ => gram_nonneg a _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BoundedSplit d X => (1:ℝ)) (fun R => gram a R.val (X+R.val))
  have hcard : (Fintype.card (BoundedSplit d X) : ℝ) ≤ (2:ℝ)^(4*d^2) := by
    have h := card_bounded_splits_le d X
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ R : BoundedSplit d X, gram a R.val (X+R.val))^2 := by nlinarith
    _ ≤ (Fintype.card (BoundedSplit d X):ℝ) *
        ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by simpa using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem split_gram_energy_le (a : G → ℝ) (d : ℕ) :
    (∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2) ≤
      predecessorEnergy a ^ 2 := by
  calc
    _ ≤ ∑ X, ∑ R : G, gram a R (X+R)^2 := by
      apply Finset.sum_le_sum
      intro X _
      exact F1Gram.sum_comp_le (fun R : BoundedSplit d X => R.val)
        Subtype.val_injective (fun R => gram a R (X+R)^2) (fun _ => sq_nonneg _)
    _ = ∑ R, ∑ S, gram a R S^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R (fun S => gram a R S^2)
    _ ≤ predecessorEnergy a ^ 2 := F1Gram.gram_energy_le (predecessorCoefficient a)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, goodConvolution a X^2) ≤ (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
  have he := predecessor_energy_le a d hdegree
  have hn := predecessor_energy_nonneg a
  have hb : 0 ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by positivity
  calc
    _ ≤ (2:ℝ)^(4*d^2) *
        ∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun X _ => goodConvolution_sq_le a d hdegree X)
    _ ≤ (2:ℝ)^(4*d^2) * predecessorEnergy a^2 :=
      mul_le_mul_of_nonneg_left (split_gram_energy_le a d) (by positivity)
    _ ≤ (2:ℝ)^(4*d^2) * ((2:ℝ)^(d^2) * ∑ Y, a Y^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      omega

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in

theorem abs_complement_sum_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    |∑ Y, if bad Y then 0 else a Y * a (X+Y)| ≤ goodConvolution a X := by
  calc
    _ ≤ ∑ Y, |if bad Y then 0 else a Y * a (X+Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ goodConvolution a X := by
      apply Finset.sum_le_sum
      intro Y _
      by_cases hb : bad Y
      · simp only [ite_eq_left hb, abs_zero]
        split <;> positivity
      · simp only [ite_eq_right hb, ite_eq_left (hcover Y hb), abs_mul, le_refl]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem convolution_split_square_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 +
      2 * (∑ Y, if bad Y then a Y * a (X+Y) else 0)^2 := by
  let u : ℝ := ∑ Y, if bad Y then 0 else a Y * a (X+Y)
  let v : ℝ := ∑ Y, if bad Y then a Y * a (X+Y) else 0
  have hs : (∑ Y, a Y * a (X+Y)) = u+v := by
    dsimp only [u,v]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hb : bad Y <;> simp only [hb, ite_true, ite_false, add_zero, zero_add]
  have hu : |u| ≤ goodConvolution a X := abs_complement_sum_le a X bad hcover
  have hp := mul_nonneg (sub_nonneg.mpr hu)
    (add_nonneg (goodConvolution_nonneg a X) (abs_nonneg u))
  have hu2 : u^2 ≤ goodConvolution a X^2 := by nlinarith [sq_abs u]
  change (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 + 2*v^2
  rw [hs]
  nlinarith [sq_nonneg (u-v)]

omit [FiniteDimensional F2 F] in
theorem convolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (bad : G → G → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (∑ X, (∑ Y, a Y * a (X+Y))^2) ≤
      2 * ((2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
  calc
    _ ≤ ∑ X, (2 * goodConvolution a X^2 +
        2 * (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2) :=
      Finset.sum_le_sum (fun X _ => convolution_split_square_le a X (bad X) (hcover X))
    _ = 2 * (∑ X, goodConvolution a X^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (goodConvolution_energy_le a d hdegree)
        (show (0:ℝ) ≤ 2 by norm_num)) le_rfl

variable [Fintype (F →ₗ[F2] E)]
open DFVSGames.Fourier.MatrixFourier DFVSGames.Fourier.MatrixProducts

theorem fourier_goodConvolution_energy_le (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, goodConvolution (linearCoeff f) X^2) ≤
      (2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2 := by
  simpa only [linear_parseval] using goodConvolution_energy_le (linearCoeff f) d hdegree

theorem fourth_moment_le_good_bad (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0)
    (bad : (F →ₗ[F2] E) → (F →ₗ[F2] E) → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (𝔼 X, f X^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2) +
      2 * ∑ X, (∑ Y, if bad X Y then linearCoeff f Y * linearCoeff f (X+Y) else 0)^2 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  unfold coefficientConvolution
  simpa only [linear_parseval] using
    convolution_energy_le (linearCoeff f) d hdegree bad hcover

end DFVSGames.Appendix.F1Energy
end

end OAI

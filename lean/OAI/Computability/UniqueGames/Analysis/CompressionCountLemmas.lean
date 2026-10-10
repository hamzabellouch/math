import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

/-- Canonical rank-`dim U` map. -/
def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

/-- Compress by restricting to the second domain factor and taking the second
codomain coordinate. -/
def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

/-- The actual rank-order compression fiber; subtraction agrees with addition
over the binary field. -/
def Fiber (Z : K →ₗ[F2] C) :=
  {Y : (U × K) →ₗ[F2] (U × C) //
    finrank F2 Y.range = finrank F2 U + finrank F2 (Y - base U K C).range ∧
      compress Y = Z}

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def inclusion (Z : K →ₗ[F2] C) : (U × Z.range) →ₗ[F2] (U × C) :=
  (LinearMap.id : U →ₗ[F2] U).prodMap Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

/-- The block matrix `[I+FH,FZ;H,Z]`. -/
def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

theorem graph_injective (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Function.Injective (graph Z F) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

theorem inclusion_injective (Z : K →ₗ[F2] C) :
    Function.Injective (inclusion (U := U) Z) := by
  intro a b h
  exact Prod.ext (by simpa [inclusion] using congrArg Prod.fst h)
    (Subtype.ext (by simpa [inclusion] using congrArg Prod.snd h))

theorem lower_surjective (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    Function.Surjective (lower Z H) := by
  intro c
  obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
  refine ⟨(0, k), ?_⟩
  simpa [lower] using hk

theorem range_lift_sub_base (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P - base U K C).range = (graph Z P.1).range := by
  rw [lift, add_sub_cancel_left]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (lower_surjective Z P.2))

theorem range_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P).range = (inclusion (U := U) Z).range := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨(p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      P.2 p.1 + Z.rangeRestrict p.2), ?_⟩
    simp [inclusion]
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict (c - P.2 (u - P.1 c))
    refine ⟨(u - P.1 c, k), ?_⟩
    have hc : P.2 (u - P.1 c) + Z.rangeRestrict k = c := by rw [hk]; abel
    apply Prod.ext
    · change u - P.1 c + P.1 (P.2 (u - P.1 c) + Z.rangeRestrict k) = u
      rw [hc]
      abel
    · simpa [inclusion] using congrArg Subtype.val hc

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K]

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] in
theorem finrank_base : finrank F2 (base U K C).range = finrank F2 U := by
  rw [base, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr LinearMap.fst_surjective)]
  exact LinearMap.finrank_range_of_inj LinearMap.inl_injective

theorem lift_rank_order (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    finrank F2 (lift Z P).range =
      finrank F2 U + finrank F2 (lift Z P - base U K C).range := by
  rw [range_lift, range_lift_sub_base,
    LinearMap.finrank_range_of_inj (inclusion_injective (U := U) Z),
    LinearMap.finrank_range_of_inj (graph_injective Z P.1), Module.finrank_prod]

def toFiber (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) : Fiber (U := U) Z :=
  ⟨lift Z P, lift_rank_order Z P, compress_lift Z P⟩

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] in
theorem lift_injective (Z : K →ₗ[F2] C) :
    Function.Injective (lift (U := U) Z) := by
  rintro ⟨F, H⟩ ⟨G, J⟩ h
  have hH : H = J := by
    ext u
    have he := congrArg (fun f => (f (u, 0)).2) h
    simpa using he
  have hF : F = G := by
    ext c
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
    have he := congrArg (fun f => (f (0, k)).1) h
    simpa [hk] using he
  exact Prod.ext hF hH

theorem natCard_linearMap [FiniteDimensional F2 C] : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

/-- Rank additivity supplies exactly the image/kernel hypotheses used by the
block argument. -/
theorem fiber_geometry (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Disjoint (base U K C).range (Y.val - base U K C).range ∧
      (base U K C).ker ⊔ (Y.val - base U K C).ker = ⊤ := by
  apply (RankAdditivity.finrank_add_eq_iff (base U K C) (Y.val - base U K C)).mp
  have heq : base U K C + (Y.val - base U K C) = Y.val := by abel
  rw [heq, finrank_base]
  exact Y.property.1

/-- Every lower coordinate of a map in the fiber lies in the compressed image.
This is the step that permits taking `H : U → range Z`. -/
theorem snd_mem_range (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    (Y.val p).2 ∈ Z.range := by
  have hp : p ∈ (base U K C).ker ⊔ (Y.val - base U K C).ker := by
    rw [(fiber_geometry Z Y).2]
    trivial
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
  have ha0 : a.1 = 0 := congrArg Prod.fst ha
  have haeq : a = (0, a.2) := Prod.ext ha0 rfl
  have hDb : Y.val b = base U K C b := sub_eq_zero.mp hb
  refine ⟨a.2, ?_⟩
  have hcomp := LinearMap.congr_fun Y.property.2 a.2
  calc
    Z a.2 = (Y.val (0, a.2)).2 := hcomp.symm
    _ = (Y.val a).2 := congrArg (fun q => (Y.val q).2) haeq.symm
    _ = (Y.val (a + b)).2 := by simp [map_add, hDb]
    _ = (Y.val p).2 := congrArg (fun q => (Y.val q).2) hab

/-- Choose a linear section of the map onto its image. -/
noncomputable def linearSection (Z : K →ₗ[F2] C) : Z.range →ₗ[F2] K :=
  Classical.choose
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)

theorem section_spec (Z : K →ₗ[F2] C) (c : Z.range) :
    Z.rangeRestrict (linearSection Z c) = c :=
  LinearMap.congr_fun (Classical.choose_spec
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)) c

noncomputable def extractedF (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Z.range →ₗ[F2] U :=
  (LinearMap.fst F2 U C).comp
    (Y.val.comp ((LinearMap.inr F2 U K).comp (linearSection Z)))

def extractedH (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 U C).comp (Y.val.comp (LinearMap.inl F2 U K))).codRestrict
    Z.range (fun u => snd_mem_range Z Y (u, 0))

theorem extracted_lower (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    extractedH Z Y p.1 + Z.rangeRestrict p.2 =
      ⟨(Y.val p).2, snd_mem_range Z Y p⟩ := by
  apply Subtype.ext
  change (Y.val (p.1, 0)).2 + Z p.2 = (Y.val p).2
  rw [← LinearMap.congr_fun Y.property.2 p.2]
  change (Y.val (p.1, 0)).2 + (Y.val (0, p.2)).2 = (Y.val p).2
  rw [← Prod.snd_add, ← map_add]
  simp

/-- On the difference image, the lower coordinate uniquely determines the
upper coordinate. -/
theorem difference_ext_snd (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z)
    (p q : U × K) (h : (Y.val p).2 = (Y.val q).2) :
    (Y.val - base U K C) p = (Y.val - base U K C) q := by
  let D := Y.val - base U K C
  have hbottom : (D (p - q)).2 = 0 := by
    change ((Y.val - base U K C) (p - q)).2 = 0
    simp only [LinearMap.sub_apply, map_sub, Prod.snd_sub, base_apply]
    simpa using sub_eq_zero.mpr h
  have hzero : D (p - q) = 0 := by
    apply Submodule.disjoint_def.mp (fiber_geometry Z Y).1 (D (p - q))
    · refine ⟨((D (p - q)).1, 0), ?_⟩
      exact Prod.ext rfl hbottom.symm
    · exact ⟨p - q, rfl⟩
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

theorem lift_extracted (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    lift Z (extractedF Z Y, extractedH Z Y) = Y.val := by
  apply LinearMap.ext
  intro p
  let c : Z.range := ⟨(Y.val p).2, snd_mem_range Z Y p⟩
  have hq : (Y.val (0, linearSection Z c)).2 = (Y.val p).2 := by
    calc
      (Y.val (0, linearSection Z c)).2 = Z (linearSection Z c) :=
        LinearMap.congr_fun Y.property.2 (linearSection Z c)
      _ = (c : C) := congrArg Subtype.val (section_spec Z c)
      _ = (Y.val p).2 := rfl
  have hd := congrArg Prod.fst (difference_ext_snd Z Y p (0, linearSection Z c) hq.symm)
  change (Y.val p).1 - p.1 = (Y.val (0, linearSection Z c)).1 - 0 at hd
  apply Prod.ext
  · change p.1 + extractedF Z Y
      (extractedH Z Y p.1 + Z.rangeRestrict p.2) = (Y.val p).1
    rw [extracted_lower]
    change p.1 + (Y.val (0, linearSection Z c)).1 = (Y.val p).1
    rw [sub_zero] at hd
    rw [← hd]
    abel
  · simpa using congrArg Subtype.val (extracted_lower Z Y p)

theorem toFiber_bijective (Z : K →ₗ[F2] C) :
    Function.Bijective (toFiber (U := U) Z) := by
  constructor
  · intro P Q h
    exact lift_injective Z (congrArg Subtype.val h)
  · intro Y
    exact ⟨(extractedF Z Y, extractedH Z Y), Subtype.ext (lift_extracted Z Y)⟩

/-- The exact compression fiber is in bijection with two independent spaces of
linear maps. No rank or cardinality claim is an assumption of this equivalence. -/
noncomputable def fiberEquiv (Z : K →ₗ[F2] C) :
    Parameters (U := U) Z ≃ Fiber (U := U) Z :=
  Equiv.ofBijective (toFiber Z) (toFiber_bijective Z)

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

/-- Lemma A.2 in arbitrary finite-dimensional block coordinates. -/
theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

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

section Binary

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

end Binary

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A complement to the kernel maps isomorphically onto the range. -/
def complementRangeEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : P ≃ₗ[𝕜] X.range :=
  (X.ker.quotientEquivOfIsCompl P hP).symm.trans X.quotKerEquivRange

@[simp] theorem complementRangeEquiv_apply (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (p : P) :
    (complementRangeEquiv X P hP p : F) = X p := by
  rfl

/-- Domain coordinates, with the first coordinate literally in `range X`. -/
def domainEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : (X.range × X.ker) ≃ₗ[𝕜] E :=
  (LinearEquiv.prodCongr (complementRangeEquiv X P hP).symm
    (LinearEquiv.refl 𝕜 X.ker)).trans (P.prodEquivOfIsCompl X.ker hP.symm)

/-- The domain equivalence exhibits precisely the image coordinate of X. -/
@[simp] theorem apply_domainEquiv (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (u : X.range) (k : X.ker) :
    X (domainEquiv X P hP (u, k)) = (u : F) := by
  change X ((complementRangeEquiv X P hP).symm u + (k : E)) = (u : F)
  rw [map_add, show X (k : E) = 0 from k.property, add_zero]
  have h := congrArg (fun v : X.range => (v : F))
    ((complementRangeEquiv X P hP).apply_symm_apply u)
  simpa only [complementRangeEquiv_apply] using h

/-- Codomain coordinates split the range off from a chosen complement. -/
def codomainEquiv (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) : (X.range × C) ≃ₗ[𝕜] F :=
  X.range.prodEquivOfIsCompl C hC

/-- An arbitrary map has the canonical compression-fiber block form. -/
theorem canonical_block (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (u : X.range) (k : X.ker) :
    (codomainEquiv X C hC).symm (X (domainEquiv X P hP (u, k))) = (u, 0) := by
  rw [apply_domainEquiv]
  exact Submodule.prodEquivOfIsCompl_symm_apply_left X.range C hC u

/-- Choice of complements is available over every field; this is an actual
normal-form existence result, including zero-dimensional kernel/range cases. -/
theorem exists_canonical_coordinates (X : E →ₗ[𝕜] F) :
    ∃ (P : Submodule 𝕜 E) (C : Submodule 𝕜 F)
      (hP : IsCompl X.ker P) (hC : IsCompl X.range C),
      ∀ (u : X.range) (k : X.ker),
        (codomainEquiv X C hC).symm (X (domainEquiv X P hP (u, k))) = (u, 0) := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  exact ⟨P, C, hP, hC, canonical_block X P hP C hC⟩

@[simp] theorem domainEquiv_zero_left (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (k : X.ker) :
    domainEquiv X P hP (0, k) = (k : E) := by
  change ((complementRangeEquiv X P hP).symm 0 : E) + (k : E) = (k : E)
  simp

theorem quotient_coordinates (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (v : F) :
    X.range.quotientEquivOfIsCompl C hC (X.range.mkQ v) =
      ((codomainEquiv X C hC).symm v).2 := by
  simp [codomainEquiv, Submodule.prodEquivOfIsCompl_symm_apply]

/-- Re-express all maps in the chosen domain/codomain coordinates at once. -/
def toBlocks (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    (E →ₗ[𝕜] F) ≃ₗ[𝕜] ((X.range × X.ker) →ₗ[𝕜] (X.range × C)) :=
  LinearEquiv.arrowCongr (domainEquiv X P hP).symm (codomainEquiv X C hC).symm

@[simp] theorem toBlocks_apply (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (u : X.range) (k : X.ker) :
    toBlocks X P hP C hC Y (u, k) =
      (codomainEquiv X C hC).symm (Y (domainEquiv X P hP (u, k))) := by
  rfl

/-- The lower-right block is exactly the original quotient restriction,
transported through the quotient/complement equivalence. -/
theorem compressed_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (k : X.ker) :
    (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (X.range.mkQ (Y k)) := by
  rw [toBlocks_apply, domainEquiv_zero_left, quotient_coordinates]

theorem toBlocks_base (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    toBlocks X P hP C hC X =
      (LinearMap.inl 𝕜 X.range C).comp (LinearMap.fst 𝕜 X.range X.ker) := by
  apply LinearMap.ext
  intro p
  exact canonical_block X P hP C hC p.1 p.2

section RankTransport

variable {U V : Type*} [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup V] [Module 𝕜 V]

/-- Changing coordinates induces a genuine linear equivalence on ranges. -/
def rangeTransport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V) (Y : E →ₗ[𝕜] F) :
    Y.range ≃ₗ[𝕜] (LinearEquiv.arrowCongr e f Y).range where
  toFun y := ⟨f y, by
    obtain ⟨w, hw⟩ := y.property
    exact ⟨e w, by simp [LinearEquiv.arrowCongr_apply, hw]⟩⟩
  invFun z := ⟨f.symm z, by
    obtain ⟨u, hu⟩ := z.property
    refine ⟨e.symm u, ?_⟩
    have h := congrArg f.symm hu
    simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply] using h⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by apply Subtype.ext; simp

theorem finrank_range_transport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V)
    (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearEquiv.arrowCongr e f Y).range =
      Module.finrank 𝕜 Y.range :=
  (rangeTransport e f Y).finrank_eq.symm

end RankTransport

theorem finrank_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    Module.finrank 𝕜 (toBlocks X P hP C hC Y).range =
      Module.finrank 𝕜 Y.range :=
  finrank_range_transport (domainEquiv X P hP).symm (codomainEquiv X C hC).symm Y

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

end

end OAI

import OAI.Computability.UniqueGames.Analysis.A13IndexLemmas
import OAI.Computability.UniqueGames.Analysis.A5IndexCount
import OAI.Computability.UniqueGames.Analysis.A5ReverseIndex
import OAI.Computability.UniqueGames.Analysis.HybridCompositionLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

namespace Appendix.A5FrequencyTransport

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.NaturalTransport

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem quotient_relativeFrequency_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (A5ReverseIndex.relativeFrequency A A' B' B hA hB Y b) =
    Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b) := by
  change Submodule.quotientQuotientEquivQuotient A A' hA
      ((Submodule.quotientQuotientEquivQuotient A A' hA).symm
        (Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b))) = _
  exact (Submodule.quotientQuotientEquivQuotient A A' hA).apply_symm_apply _

theorem quotient_compress_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (X : B →ₗ[F2] (V ⧸ A)) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (compress X (A'.map A.mkQ) (B'.comap B.subtype) b) =
    Submodule.mapQ A A' LinearMap.id hA (X b.val) := rfl

/-- The relative compression equation follows from the concrete map to the
direct quotient on each element of the retained subspace. -/
theorem compression_eq_relativeFrequency_of_pointwise
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) (Y : B' →ₗ[F2] (V ⧸ A'))
    (hY : ∀ b : B', Submodule.mapQ A A' LinearMap.id hA
      (X ⟨b.val, hB b.property⟩) = Y b) :
    compress X (A'.map A.mkQ) (B'.comap B.subtype) =
      A5ReverseIndex.relativeFrequency A A' B' B hA hB Y := by
  ext b
  apply (Submodule.quotientQuotientEquivQuotient A A' hA).injective
  rw [quotient_compress_apply, quotient_relativeFrequency_apply]
  exact hY ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]
  [Finite V] [Finite W]

omit [FiniteDimensional F2 V] [Finite V] in
theorem quotientFactor_mapQ
    (A : Submodule F2 V) (C : Submodule F2 (V ⧸ A))
    (hA : A ≤ C.comap A.mkQ) (u : V ⧸ A) :
    quotientFactor A C
      (Submodule.mapQ A (C.comap A.mkQ) LinearMap.id hA u) = C.mkQ u := by
  obtain ⟨x, rfl⟩ := A.mkQ_surjective u
  change quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x)
  exact quotientFactor_mkQ A C x

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem dualFactor_quotient
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((V ⧸ A) ⧸ C)) (b : D.map B.subtype) :
    quotientFactor A C (dualFactor A B C D Z b) =
      Z ((outputFactor B D).symm b) := by
  change quotientFactor A C ((quotientFactor A C).symm
    (Z ((outputFactor B D).symm b))) = _
  exact (quotientFactor A C).apply_symm_apply _

omit [FiniteDimensional F2 W] [Finite W] in
theorem outputFactor_symm_as_inclusion
    (B : Submodule F2 W) (D : Submodule F2 B)
    (hB : D.map B.subtype ≤ B) (b : D.map B.subtype) :
    (((outputFactor B D).symm b : D) : B) = ⟨b.val, hB b.property⟩ := by
  apply Subtype.ext
  have hh := outputFactor_val B D ((outputFactor B D).symm b)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- The naturally transported local compression belongs to the precise
relative-frequency fiber used in `A5ReverseIndex.Ancestor`. -/
theorem compression_eq_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) :
    compress X ((C.comap A.mkQ).map A.mkQ) ((D.map B.subtype).comap B.subtype) =
      A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D)) := by
  apply compression_eq_relativeFrequency_of_pointwise
  intro b
  apply (quotientFactor A C).injective
  rw [quotientFactor_mapQ, dualFactor_quotient]
  change C.mkQ (X ⟨b.val, hB b.property⟩) =
    C.mkQ (X (((outputFactor B D).symm b : D) : B))
  rw [outputFactor_symm_as_inclusion B D hB b]

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- Package the actual naturally transported label into its counted
antecedent fiber, retaining the original map as the witness. -/
theorem isAntecedent_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A))
    (hdis : Disjoint X.range C) (hcover : D ⊔ X.ker = ⊤) :
    AntecedentCount.IsAntecedent ((D.map B.subtype).comap B.subtype)
      ((C.comap A.mkQ).map A.mkQ)
      (A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D))) X := by
  refine ⟨compression_eq_relativeFrequency_dualFactor A B C D hA hB X, ?_, ?_⟩
  · rw [Submodule.map_comap_eq_of_surjective A.mkQ_surjective C]
    exact hdis
  · rw [Submodule.comap_map_eq_of_injective (f := B.subtype) Subtype.val_injective D]
    exact hcover

end Appendix.A5FrequencyTransport

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

namespace Appendix.A5Passage

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev OuterIndex (X : F →ₗ[F2] E) (e : Nat) :=
  HybridIndex (E := E ⧸ X.range) (F := X.ker) e

def LiftedA (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 E :=
  s.val.1.comap X.range.mkQ

def LiftedB (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 F :=
  s.val.2.map X.ker.subtype

abbrev Pair (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :=
  OperatorPartitions.A5GeometricIndex X (LiftedA X s) (LiftedB X s)

abbrev Passage (X : F →ₗ[F2] E) (e : Nat) :=
  Σ s : OuterIndex X e, Pair X s

theorem comap_mkQ_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 (E ⧸ P) => A.comap P.mkQ) := by
  intro A B h
  change A.comap P.mkQ = B.comap P.mkQ at h
  ext z
  obtain ⟨v, rfl⟩ := P.mkQ_surjective z
  change v ∈ A.comap P.mkQ ↔ v ∈ B.comap P.mkQ
  rw [h]

theorem map_subtype_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 P => A.map P.subtype) := by
  intro A B h
  change A.map P.subtype = B.map P.subtype at h
  ext z
  constructor
  · intro hz
    have hm : (z : E) ∈ A.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv
  · intro hz
    have hm : (z : E) ∈ B.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv

theorem outer_eq_of_lifted (X : F →ₗ[F2] E) {e : Nat} (s t : OuterIndex X e)
    (hA : LiftedA X s = LiftedA X t) (hB : LiftedB X s = LiftedB X t) : s = t := by
  apply Subtype.ext
  exact Prod.ext (comap_mkQ_injective X.range hA) (map_subtype_injective X.ker hB)

theorem recover_liftedA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    LiftedA X q.1 = q.2.val.1 ⊔ X.range := q.2.property.2.1.symm

theorem recover_liftedB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    LiftedB X q.1 = q.2.val.2 ⊓ X.ker := q.2.property.2.2.2.symm

def forget (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    Submodule F2 E × Submodule F2 F := q.2.val

theorem forget_injective (X : F →ₗ[F2] E) (e : Nat) :
    Function.Injective (forget X e) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  change p.val = q.val at h
  have hA : LiftedA X s = LiftedA X t := by
    calc
      LiftedA X s = p.val.1 ⊔ X.range := p.property.2.1.symm
      _ = q.val.1 ⊔ X.range := congrArg (fun A => A ⊔ X.range) (congrArg Prod.fst h)
      _ = LiftedA X t := q.property.2.1
  have hB : LiftedB X s = LiftedB X t := by
    calc
      LiftedB X s = p.val.2 ⊓ X.ker := p.property.2.2.2.symm
      _ = q.val.2 ⊓ X.ker := congrArg (fun B => B ⊓ X.ker) (congrArg Prod.snd h)
      _ = LiftedB X t := q.property.2.2.2
  have hst := outer_eq_of_lifted X s t hA hB
  cases hst
  have hpq : p = q := Subtype.ext h
  cases hpq
  rfl

@[simp] theorem forget_val (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    forget X e q = q.2.val := rfl

variable [Finite E] [Finite F]

instance pairFintype (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :
    Fintype (Pair X s) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dim_pairA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 q.2.val.1 = Module.finrank F2 q.1.val.1 := by
  have hsup := q.2.val.1.finrank_sup_add_finrank_inf_eq X.range
  rw [q.2.property.2.1, q.2.property.1.eq_bot, finrank_bot, add_zero] at hsup
  have hcomap := HybridComposition.finrank_comap_mkQ X.range q.1.val.1
  change Module.finrank F2 (LiftedA X q.1) =
    Module.finrank F2 X.range + Module.finrank F2 q.1.val.1 at hcomap
  omega

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem codim_pairB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (F ⧸ q.2.val.2) =
      Module.finrank F2 (X.ker ⧸ q.1.val.2) := by
  have hsup := q.2.val.2.finrank_sup_add_finrank_inf_eq X.ker
  rw [q.2.property.2.2.1, q.2.property.2.2.2, finrank_top] at hsup
  have hmap := Submodule.finrank_map_subtype_eq X.ker q.1.val.2
  change Module.finrank F2 (LiftedB X q.1) = Module.finrank F2 q.1.val.2 at hmap
  have hF := q.2.val.2.finrank_quotient_add_finrank
  have hK := q.1.val.2.finrank_quotient_add_finrank
  change Module.finrank F2 (X.ker ⧸ q.1.val.2) + Module.finrank F2 q.1.val.2 =
    Module.finrank F2 X.ker at hK
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 := by
  unfold UniqueGamesTheorem.Fourier.MatrixRestrictions.order
  rw [dim_pairA X q, codim_pairB X q]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order_le (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 ≤ e := by
  rw [pair_order]
  exact q.1.property

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_rank (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (LinearIdentities.compress X q.2.val.1 q.2.val.2).range =
      Module.finrank F2 X.range :=
  LinearIdentities.compress_rank_preserved X q.2.val.1 q.2.val.2
    q.2.property.1 q.2.property.2.2.1

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
      (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      Module.finrank F2 X.range := by
  rw [NaturalTransport.dualFactor_rank]
  exact pair_rank X q

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 +
        Module.finrank F2 X.range := by
  rw [HybridComposition.order_effective, NaturalTransport.dualFactor_rank,
    pair_order, pair_rank]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_le (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (d : Nat)
    (h : UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range ≤ d)
    (q : Passage X (d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
      Module.finrank F2 X.range))) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range ≤ d := by
  rw [effective_order_rank]
  have hq := q.1.property
  change UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 ≤
    d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range) at hq
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_pos (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat}
    (h : 0 < UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range)
    (q : Passage X e) :
    0 < UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range := by
  rw [effective_order_rank]
  omega

def descendantSum (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : Passage X e,
    𝔼 U, (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2) ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem descendantSum_nonneg (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ descendantSum A B X e f := by
  exact Finset.sum_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => sq_nonneg _

end Appendix.A5Passage

namespace Appendix.A5ForwardIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

abbrev Index (d : ℕ) :=
  Σ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
    A5Passage.Passage r.val.2.2 (d - A13Index.size r.val)

def descendant {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.Triple (E := E) (F := F) :=
  ⟨a.2.2.val.1.comap a.1.val.1.mkQ, a.2.2.val.2.map a.1.val.2.1.subtype,
    NaturalTransport.dualFactor a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
      (LinearIdentities.compress a.1.val.2.2 a.2.2.val.1 a.2.2.val.2)⟩

def sourceI {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 a.1.val.1

def sourceJ {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 (F ⧸ a.1.val.2.1)

def targetRank (r : A13Index.Triple (E := E) (F := F)) : ℕ :=
  Module.finrank F2 r.2.2.range

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank {d : ℕ} (a : Index (E := E) (F := F) d) :
    targetRank (descendant a) = Module.finrank F2 a.1.val.2.2.range :=
  A5Passage.descendant_rank a.1.val.1 a.1.val.2.1 a.1.val.2.2 a.2

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_size {d : ℕ} (a : Index (E := E) (F := F) d) :
    sourceI a + sourceJ a + targetRank (descendant a) = A13Index.size a.1.val := by
  rw [descendant_rank]
  rfl

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_order_bounds {d : ℕ} (a : Index (E := E) (F := F) d) :
    1 ≤ sourceI a + sourceJ a + targetRank (descendant a) ∧
      sourceI a + sourceJ a + targetRank (descendant a) ≤ d := by
  rw [original_size]
  exact a.1.property

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_size_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.size (descendant a) ≤ d :=
  A5Passage.effective_order_rank_le a.1.val.1 a.1.val.2.1 a.1.val.2.2 d
    a.1.property.2 a.2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierA_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    a.1.val.1 ≤ (descendant a).1 := by
  intro x hx
  change a.1.val.1.mkQ x ∈ a.2.2.val.1
  rw [show a.1.val.1.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact a.2.2.val.1.zero_mem

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierB_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    (descendant a).2.1 ≤ a.1.val.2.1 := by
  rintro x ⟨b, hb, rfl⟩
  exact b.property

abbrev Fiber (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :=
  {a : Index (E := E) (F := F) d //
    descendant a = r ∧ sourceI a = i ∧ sourceJ a = j}

/-- The encoder keeps the actual earlier pair and actual earlier map. -/
def encode (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ)
    (a : Fiber d r i j) : A5ReverseIndex.Ancestor r.1 r.2.1 r.2.2 i j := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  refine ⟨⟨a.1.val.1, earlierA_le a, hi⟩,
    ⟨a.1.val.2.1, earlierB_le a, hj⟩, ⟨a.1.val.2.2, ?_⟩⟩
  exact A5FrequencyTransport.isAntecedent_relativeFrequency_dualFactor
    a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
    (earlierA_le a) (earlierB_le a) a.1.val.2.2
    a.2.2.property.1.symm a.2.2.property.2.2.1

def earlierTriple {A' : Submodule F2 E} {B' : Submodule F2 F}
    {Y : B' →ₗ[F2] (E ⧸ A')} {i j : ℕ}
    (a : A5ReverseIndex.Ancestor A' B' Y i j) : A13Index.Triple (E := E) (F := F) :=
  ⟨a.1.val, a.2.1.val, a.2.2.val⟩

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierTriple_encode (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) (a : Fiber d r i j) :
    earlierTriple (encode d r i j a) = a.val.1.val := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Fixing the result and retained earlier data fixes both the complementary
pair and its outer hybrid index. No additional outer-index factor occurs. -/
theorem encode_injective (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Function.Injective (encode d r i j) := by
  intro a b hab
  have hraw : a.val.1.val = b.val.1.val := by
    simpa only [earlierTriple_encode] using congrArg earlierTriple hab
  have hbase : a.val.1 = b.val.1 := Subtype.ext hraw
  have hresult : descendant a.val = descendant b.val := a.property.1.trans b.property.1.symm
  rcases a with ⟨⟨r₁, p⟩, ha⟩
  rcases b with ⟨⟨r₂, q⟩, hb⟩
  change r₁ = r₂ at hbase
  cases hbase
  have hA := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.1) hresult
  have hB := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.2.1) hresult
  change p.2.val.1.comap r₁.val.1.mkQ = q.2.val.1.comap r₁.val.1.mkQ at hA
  change p.2.val.2.map r₁.val.2.1.subtype = q.2.val.2.map r₁.val.2.1.subtype at hB
  have hpq : p = q := A5Passage.forget_injective r₁.val.2.2 _
    (Prod.ext (A5Passage.comap_mkQ_injective r₁.val.1 hA)
      (A5Passage.map_subtype_injective r₁.val.2.1 hB))
  cases hpq
  rfl

local instance indexFintype (d : ℕ) : Fintype (Index (E := E) (F := F) d) := by
  letI := A13Index.boundedPositiveTripleFintype (E := E) (F := F) d
  exact inferInstance

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Actual cardinality bound for every fiber used by the weighted reversal. -/
theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r))) := by
  by_cases hn : Nonempty (Fiber d r i j)
  · obtain ⟨a⟩ := hn
    have hsize : A13Index.size r ≤ d := by
      rw [← a.property.1]
      exact descendant_size_le a.val
    have hA : Module.finrank F2 r.1 ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have hB : Module.finrank F2 (F ⧸ r.2.1) ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have ht : i + j + targetRank r ≤ d := by
      have h := (original_order_bounds a.val).2
      rwa [a.property.1, a.property.2.1, a.property.2.2] at h
    have hcount := A5ReverseIndex.card_ancestor_le_source r.1 r.2.1 r.2.2
      d i j (targetRank r) (le_refl _) hA hB ht
    exact (Nat.card_le_card_of_injective (encode d r i j)
      (encode_injective d r i j)).trans hcount
  · have : IsEmpty (Fiber d r i j) := ⟨fun a => hn ⟨a⟩⟩
    simp

end Appendix.A5ForwardIndex

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

namespace Appendix.A5ReverseSum

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def actualMoment (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  𝔼 T, (𝔼 N, mapDerivative r.2.2 (hybridDerivative r.1 r.2.1 T f) N ^ 2) ^ 2

def targetWeight (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  if order r.1 r.2.1 ≤ d then actualMoment f r else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem targetWeight_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : 0 ≤ targetWeight d f r := by
  unfold targetWeight
  split_ifs
  · exact Finset.expect_nonneg fun _ _ => sq_nonneg _
  · exact le_refl _

theorem targetWeight_descendant (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    targetWeight d f (descendant a) = actualMoment f (descendant a) := by
  have h := descendant_size_le a
  have ho : order (descendant a).1 (descendant a).2.1 ≤ d := by
    unfold A13Index.size at h
    omega
  exact ite_eq_left ho

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- The target cutoff is exactly the actual finite hybrid index. -/
theorem sum_triples_cutoff (d : ℕ)
    (H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y := by
  classical
  let G : Submodule F2 E × Submodule F2 F → ℝ :=
    fun p => ∑ Y : p.2 →ₗ[F2] (E ⧸ p.1), H p.1 p.2 Y
  have hh : (∑ s : HybridIndex (E := E) (F := F) d, G s.val) =
      ∑ p : Submodule F2 E × Submodule F2 F,
        if order p.1 p.2 ≤ d then G p else 0 := by
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Submodule F2 E × Submodule F2 F =>
            order p.1 p.2 ≤ d), G p := by
        exact (Finset.sum_subtype _ (by simp) G).symm
      _ = _ := Finset.sum_filter _ _
  change _ = ∑ s : HybridIndex (E := E) (F := F) d, G s.val
  rw [hh, Fintype.sum_prod_type]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro A _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : order A B ≤ d
  · simp only [h, ite_true, G]
  · simp only [h, ite_false, Finset.sum_const_zero]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem target_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      ((2 : ℝ)⁻¹) ^ (31 * d * (targetRank r + 1) + 4 * d * targetRank r) *
        targetWeight d f r) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
        ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
          4 * d * Module.finrank F2 Y.range) *
          (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  let H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ := fun A B Y =>
    ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
      4 * d * Module.finrank F2 Y.range) * actualMoment f ⟨A, B, Y⟩
  calc
    _ = ∑ r : A13Index.Triple (E := E) (F := F),
        if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0 := by
      apply Finset.sum_congr rfl
      rintro ⟨A, B, Y⟩ _
      simp only [targetWeight, targetRank, H, mul_ite, mul_zero]
    _ = ∑ s : HybridIndex (E := E) (F := F) d,
        ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y :=
      sum_triples_cutoff d H
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  rw [← Finset.mul_expect]
  rfl

theorem source_summand_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
      24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
      6 * d * targetRank (descendant a)) * targetWeight d f (descendant a) =
    (2 : ℝ) ^ (100 * (d - A13Index.size a.1.val) ^ 2 +
      24 * d * A13Index.size a.1.val + 6 * d * Module.finrank F2 a.1.val.2.2.range) *
        actualMoment f (descendant a) := by
  rw [original_size, descendant_rank, targetWeight_descendant]

theorem source_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ a : Index (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
        24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
        6 * d * targetRank (descendant a)) * targetWeight d f (descendant a)) =
    ∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f := by
  simp_rw [source_summand_eq]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [A5Passage.descendantSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- The weighted sum of actual A.5 descendants is bounded by damped actual
map-derivative moments over all hybrid restrictions of order at most `d`. -/
theorem weighted_descendantSum_le (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f) ≤
    (2 : ℝ) ^ (100 * d * d) *
      ∑ s : HybridIndex (E := E) (F := F) d,
        𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
          ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
            4 * d * Module.finrank F2 Y.range) *
            (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  have h := A5WeightedReindex.weighted_reindex d hd
    (descendant (E := E) (F := F) (d := d)) sourceI sourceJ targetRank
    (targetWeight d f) (targetWeight_nonneg d f) original_order_bounds
    (fun r i j => by simpa only [Nat.mul_assoc] using card_fiber_le d r i j)
  rwa [source_sum_eq, target_sum_eq] at h

end Appendix.A5ReverseSum

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

namespace Appendix.A5Induction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

/-- The strong-induction motive quantifies over the actual changing domains.
Quotients and subspaces preserve the fixed universe levels. -/
def BoundAtDegree (d : ℕ) : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    [Finite E] [Finite F]
    [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
    (f : (E →ₗ[F2] F) → ℝ),
    DegreeAtMost d f →
      (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f

theorem damping_le (d k : ℕ) :
    (1 / 2 : ℝ) ^ (31 * d * (k + 1) + 4 * d * k) ≤
      (1 / 2 : ℝ) ^ (31 * d) * (1 / 2 : ℝ) ^ (8 * d * k) := by
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
      nlinarith
  have he : 31 * d * (k + 1) + 4 * d * k =
      (31 * d + 8 * d * k) + 27 * d * k := by ring
  rw [he, pow_add, pow_add]
  have hh := mul_le_mul_of_nonneg_left (hpow (27 * d * k))
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (31 * d))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (8 * d * k)))
  simpa only [mul_one] using hh

theorem coefficient_absorption (d : ℕ) (hd : 1 ≤ d) :
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
      (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) ≤
      (2 : ℝ) ^ (100 * d * d) := by
  have hfirst : (2 : ℝ) ^ (100 * d * d) *
      ((2 : ℝ) ^ (94 * d * d))⁻¹ = (2 : ℝ) ^ (6 * d * d) := by
    have he : 100 * d * d = 6 * d * d + 94 * d * d := by ring
    rw [he, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      mul_one]
  have he : 31 * d = (31 * d - 1) + 1 := by omega
  have hsecond : ((2 : ℝ) ^ (31 * d - 1))⁻¹ =
      2 * (1 / 2 : ℝ) ^ (31 * d) := by
    calc
      ((2 : ℝ) ^ (31 * d - 1))⁻¹ = (1 / 2 : ℝ) ^ (31 * d - 1) := by
        rw [one_div, inv_pow]
      _ = 2 * ((1 / 2 : ℝ) ^ (31 * d - 1) * (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← pow_succ, ← he]
  have hscaled := mul_le_mul_of_nonneg_right (A5Scalar.absorption hd)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  calc
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) =
        162 * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
          ((2 : ℝ) ^ (31 * d - 1))⁻¹) * (2 : ℝ) ^ (100 * d * d) := by
      symm
      calc
        _ = 162 * ((2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (94 * d * d))⁻¹ +
            (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (31 * d - 1))⁻¹) := by ring
        _ = _ := by rw [hfirst, hsecond]
    _ ≤ _ := by simpa only [one_mul] using hscaled

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual weighted map-derivative sum left by the finite reindexing. -/
def dampedMapMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ X : F →ₗ[F2] E,
    (1 / 2 : ℝ) ^ (31 * d * (frequencyRank X + 1) + 4 * d * frequencyRank X) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2

theorem dampedMapMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedMapMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * (𝔼 M, f M ^ 2) ^ 2 := by
  have hterms : dampedMapMoment d f ≤ (1 / 2 : ℝ) ^ (31 * d) *
      ∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2) ^ 2 := by
    unfold dampedMapMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro X _
    have hh := mul_le_mul_of_nonneg_right (damping_le d (frequencyRank X))
      (sq_nonneg (𝔼 N, mapDerivative X f N ^ 2))
    simpa only [mul_assoc] using hh
  have hbase := weighted_fourth_derivative_energy f d (fun Y hY => hf Y hY)
  have hbase' :
      (∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2)^2) ≤ 2 * (𝔼 M, f M ^ 2)^2 := by
    simpa only [one_div, frequencyRank] using hbase
  calc
    dampedMapMoment d f ≤ _ := hterms
    _ ≤ (1 / 2 : ℝ) ^ (31 * d) * (2 * (𝔼 M, f M ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase'
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    _ = _ := by ring

def dampedHybridMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)

theorem dampedHybridMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedHybridMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f := by
  unfold dampedHybridMoment hybridMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)) ≤
        𝔼 T, (2 * (1 / 2 : ℝ) ^ (31 * d)) *
          (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2 := by
      apply Finset.expect_le_expect
      intro T _
      exact dampedMapMoment_le d _
        ((degree_hybridDerivative s.val.1 s.val.2 T f hf).mono (Nat.sub_le _ _))
    _ = _ := by rw [← Finset.mul_expect]

omit [Finite E] [Finite F] in
theorem hybridProjector_zero_pair (f : (E →ₗ[F2] F) → ℝ) :
    hybridProjector (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f = f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp [hybridProjector, linearCoeff_spectralProjector, LinearIdentities.Hybrid]

theorem energy_sq_le_hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, f M ^ 2) ^ 2 ≤ hybridMomentSum d f := by
  have hzero : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    have he : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) + Module.finrank F2 F =
        Module.finrank F2 F := by simpa using hq
    omega
  let s0 : HybridIndex (E := E) (F := F) d := ⟨(⊥, ⊤), by
    change Module.finrank F2 (⊥ : Submodule F2 E) +
      Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) ≤ d
    rw [hzero]
    simp⟩
  have havg := hybridDerivative_energy_average
    (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f
  rw [hybridProjector_zero_pair] at havg
  have hcs : (𝔼 T, 𝔼 N,
      hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 ≤
      𝔼 T, (𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 := by
    simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun T => 𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2)
      (fun _ => (1 : ℝ))
  rw [havg] at hcs
  apply hcs.trans
  change (𝔼 T, (𝔼 N, hybridDerivative s0.val.1 s0.val.2 T f N ^ 2) ^ 2) ≤ _
  unfold hybridMomentSum
  let H : HybridIndex (E := E) (F := F) d → ℝ :=
    fun s => 𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)^2
  change H s0 ≤ ∑ s, H s
  exact Finset.single_le_sum (f := H) (s := Finset.univ)
    (fun s _ => Finset.expect_nonneg (fun T _ =>
      sq_nonneg (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)))
    (Finset.mem_univ s0)

theorem degree_zero_bound (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost 0 f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * 0 * 0) * hybridMomentSum 0 f := by
  rw [DegreeZero.fourth_moment_eq_energy_sq f (fun Y hY => hf Y hY)]
  simpa using energy_sq_le_hybridMomentSum 0 f

/-- Close the actual recurrence once its finite index expansion is supplied.
This lemma states that recurrence explicitly; it is not the public A.5 theorem. -/
theorem recurrence_closure (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (hrec : (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d * d) * (𝔼 M, f M ^ 2)^2 +
        (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f := by
  have hS : 0 ≤ hybridMomentSum d f :=
    Finset.sum_nonneg (fun s _ => Finset.expect_nonneg (fun T _ => sq_nonneg _))
  have herror := mul_le_mul_of_nonneg_left (energy_sq_le_hybridMomentSum d f)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d * d))
  have hdamp := mul_le_mul_of_nonneg_left (dampedHybridMoment_le d f hf)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  have hrec' : (𝔼 M, f M ^ 4) / 162 ≤
      ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f := by
    calc
      _ ≤ _ := hrec
      _ ≤ (2 : ℝ) ^ (6 * d * d) * hybridMomentSum d f +
          (2 : ℝ) ^ (100 * d * d) *
            ((2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f) :=
        add_le_add herror hdamp
      _ = _ := by ring
  calc
    (𝔼 M, f M ^ 4) = 162 * ((𝔼 M, f M ^ 4) / 162) := by ring
    _ ≤ 162 * (((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f) := mul_le_mul_of_nonneg_left hrec' (by norm_num)
    _ = (162 * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d)))) *
          hybridMomentSum d f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_absorption d hd) hS

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Dimension bounds for the outer subspaces used by the actual A.5 operator
identity, obtained from the order of an actual derivative-space index. -/
theorem lifted_outer_dimensions (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d) :
    Module.finrank F2 (C.comap X.range.mkQ) ≤ d ∧
      Module.finrank F2 (F ⧸ D.map X.ker.subtype) ≤ d := by
  have hC := HybridComposition.finrank_comap_mkQ X.range C
  have hD := Submodule.finrank_map_subtype_eq X.ker D
  have hKD := D.finrank_quotient_add_finrank
  have hFD := (D.map X.ker.subtype).finrank_quotient_add_finrank
  have hX := X.finrank_range_add_finrank_ker
  change Module.finrank F2 X.range +
    (Module.finrank F2 C + Module.finrank F2 (X.ker ⧸ D)) ≤ d at hcut
  constructor <;> omega

/-- The native A.5 energy inequality with its actually proved numerical
complement factor. The only cutoff is the rank plus the outer derivative order. -/
theorem a5_energySquare_le_power (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    [Fintype (OperatorPartitions.A5GeometricIndex X
      (C.comap X.range.mkQ) (D.map X.ker.subtype))]
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (S : Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) ^ 2 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
        ∑ p : OperatorPartitions.A5GeometricIndex X
          (C.comap X.range.mkQ) (D.map X.ker.subtype),
          (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
            (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
  have hI : X.range ≤ C.comap X.range.mkQ := by
    intro x hx
    change X.range.mkQ x ∈ C
    have hz : X.range.mkQ x = 0 := by
      change x ∈ LinearMap.ker X.range.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map X.ker.subtype ≤ X.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hCmap : (C.comap X.range.mkQ).map X.range.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := X.range.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hDcomap : (D.map X.ker.subtype).comap X.ker.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hdims := lifted_outer_dimensions X C D d hcut
  have hcount := A5IndexCount.card_geometricIndex_cube_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI d hdims.1 hdims.2
  rw [Nat.card_eq_fintype_card] at hcount
  have hcountR :
      (Fintype.card (OperatorPartitions.A5GeometricIndex X
        (C.comap X.range.mkQ) (D.map X.ker.subtype)) : ℝ)^3 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) := by exact_mod_cast hcount
  have hn := OperatorNorm.a5_energySquare_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI hB f S
  have hfinal := hn.trans
    (mul_le_mul_of_nonneg_right hcountR
      (Finset.sum_nonneg (fun p _ => sq_nonneg _)))
  let energy (C' : Submodule F2 (E ⧸ X.range)) (D' : Submodule F2 X.ker) : ℝ :=
    (𝔼 N, hybridDerivative C' D' S (mapDerivative X f) N ^ 2)^2
  have he : energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) = energy C D :=
    congrArg₂ energy hCmap hDcomap
  change energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) ≤ _ at hfinal
  rw [he] at hfinal
  exact hfinal

/-- Actual A.5 descendants before recombining the first hybrid restriction. -/
def postA5Sum (X : F →ₗ[F2] E) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : A5Passage.Passage X e, 𝔼 S : Parameter X.range X.ker,
    (𝔼 N, mapDerivative (LinearIdentities.compress X q.2.val.1 q.2.val.2)
      (hybridDerivative q.2.val.1 q.2.val.2 (embed X.range X.ker S) f) N ^ 2)^2

theorem mapDerivative_hybridMomentSum_le (d e : ℕ) (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (hcut : Module.finrank F2 X.range + e ≤ d) :
    hybridMomentSum e (mapDerivative X f) ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) * postA5Sum X e f := by
  unfold hybridMomentSum postA5Sum
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  let : Fintype (OperatorPartitions.A5GeometricIndex X
      (s.val.1.comap X.range.mkQ) (s.val.2.map X.ker.subtype)) :=
    A5Passage.pairFintype X s
  have hs : Module.finrank F2 X.range + order s.val.1 s.val.2 ≤ d := by
    have ho := s.property
    omega
  calc
    (𝔼 S, (𝔼 N, hybridDerivative s.val.1 s.val.2 S (mapDerivative X f) N ^ 2)^2) ≤
        𝔼 S, (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
          ∑ p : A5Passage.Pair X s,
            (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
              (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
      apply Finset.expect_le_expect
      intro S _
      exact a5_energySquare_le_power X s.val.1 s.val.2 d hs f S
    _ = _ := by rw [← Finset.mul_expect, Finset.expect_sum_comm]

/-- Recombination uses the natural domain and codomain isomorphisms. The
intermediate shifts need only be the actual embedded derivative parameters. -/
theorem postA5Sum_hybrid_average (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, postA5Sum X e (hybridDerivative A B T f)) =
      A5Passage.descendantSum A B X e f := by
  unfold postA5Sum A5Passage.descendantSum
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [NaturalTransport.nested_mapDerivative_energy
    A B q.2.val.1 q.2.val.2 f]
  exact Restriction.real_translation_average
    (fun S : Parameter X.range X.ker => embed A B (embed X.range X.ker S))
    (fun U => (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2)^2)

/-- The actual A.15 induction step for one positive-order derivative triple.
The induction hypothesis is used only at the strictly smaller degree `d-t`,
on its genuine quotient-domain and kernel-codomain spaces. -/
theorem a15_of_strong_induction (d t : ℕ) (A : Submodule F2 E)
    (B : Submodule F2 F) (X : B →ₗ[F2] (E ⧸ A))
    (ht : t = order A B + Module.finrank F2 X.range)
    (htpos : 0 < t) (htd : t ≤ d)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
      (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
        A5Passage.descendantSum A B X (d - t) f := by
  have hlt : d - t < d := by omega
  have hcut : Module.finrank F2 X.range + (d - t) ≤ d := by omega
  have hpoint (T : E →ₗ[F2] F) :
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) := by
    have hdeg : DegreeAtMost (d - t) (mapDerivative X (hybridDerivative A B T f)) := by
      simpa only [ht, frequencyRank] using degree_map_hybridDerivative A B X T f hf
    have hIH := ih (d - t) hlt (mapDerivative X (hybridDerivative A B T f)) hdeg
    have hnorm := mapDerivative_hybridMomentSum_le d (d - t) X
      (hybridDerivative A B T f) hcut
    calc
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
          (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
            hybridMomentSum (d - t) (mapDerivative X (hybridDerivative A B T f)) := hIH
      _ ≤ (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
          ((2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
            postA5Sum X (d - t) (hybridDerivative A B T f)) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = _ := by rw [pow_add]; ring
  calc
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        𝔼 T, (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) :=
      Finset.expect_le_expect (fun T _ => hpoint T)
    _ = _ := by rw [← Finset.mul_expect, postA5Sum_hybrid_average]

/-- Apply the genuine lower-degree induction step to every term of the
checked A.13 sum, preserving its original positive-order cutoff. -/
theorem boundedTripleSum_le_descendants (d : ℕ)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    A13Reduction.boundedPositiveTripleSum d f ≤
      ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
        (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
          24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
          A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
            (d - A13Index.size p.val) f := by
  unfold A13Reduction.boundedPositiveTripleSum
  apply Finset.sum_le_sum
  intro p _
  have h15 := a15_of_strong_induction d (A13Index.size p.val)
    p.val.1 p.val.2.1 p.val.2.2 rfl p.property.1 p.property.2 ih f hf
  have hw := mul_le_mul_of_nonneg_left h15
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (24 * d * A13Index.size p.val))
  have he : 24 * d * A13Index.size p.val +
      (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
        6 * d * Module.finrank F2 p.val.2.2.range) =
      100 * (d - A13Index.size p.val)^2 + 24 * d * A13Index.size p.val +
        6 * d * Module.finrank F2 p.val.2.2.range := by ring
  calc
    A13Reduction.tripleTerm d p.val f ≤
        (2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          ((2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f) := hw
    _ = ((2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          (2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range)) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f := by ring
    _ = _ := by rw [← pow_add, he]

/-- Proposition A.5 on every finite-dimensional binary linear-map space,
proved by strong induction with all changing domains in the motive. -/
theorem boundAtDegree (d : ℕ) : BoundAtDegree.{u, v} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E F instE instME instF instMF instDE instDF instFiniteE instFiniteF
      instHom instDual f hf
    by_cases hz : d = 0
    · subst d
      exact degree_zero_bound f hf
    · have hd : 1 ≤ d := by omega
      have hreverse :
          (∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
            (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
              24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
              A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
                (d - A13Index.size p.val) f) ≤
            (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f := by
        simpa only [dampedHybridMoment, dampedMapMoment, frequencyRank, one_div] using
          A5ReverseSum.weighted_descendantSum_le d hd f
      have hbounded := (boundedTripleSum_le_descendants d ih f hf).trans hreverse
      have hA13 := A13Reduction.degree_reduction_truncated f d hf
      apply recurrence_closure d hd f hf
      simpa only [pow_two, Nat.mul_assoc] using
        hA13.trans (add_le_add le_rfl hbounded)

theorem derivative_inequality (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d f := by
  simpa only [pow_two, Nat.mul_assoc] using boundAtDegree.{u, v} d f hf

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI

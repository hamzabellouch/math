import Mathlib.LinearAlgebra.Isomorphisms
import OAI.Computability.UniqueGames.Analysis.A13IndexLemmas
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.OperatorPartitions
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas
import OAI.Computability.UniqueGames.Analysis.RestrictionTransport

namespace OAI

section

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.HybridComposition

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.LinearIdentities
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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
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

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
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

end UniqueGamesTheorem.Appendix.HybridComposition

end

end

section

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

namespace UniqueGamesTheorem.Appendix.OperatorNorm

theorem energy_sum_sq_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 2) ^ 2 ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, (𝔼 n, g i n ^ 2) ^ 2 := by
  classical
  let e : I → ℝ := fun i => 𝔼 n, g i n ^ 2
  let E : ℝ := 𝔼 n, (∑ i, g i n) ^ 2
  let N : ℝ := Fintype.card I
  have hE : 0 ≤ E := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have he (i : I) : 0 ≤ e i := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hs : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he i
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp (n : Ω) : (∑ i, g i n) ^ 2 ≤ N * ∑ i, g i n ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) (fun i => g i n))
  have hEbound : E ≤ N * ∑ i, e i := by
    calc
      E ≤ 𝔼 n, N * ∑ i, g i n ^ 2 :=
        Finset.expect_le_expect fun n _ => hp n
      _ = N * ∑ i, e i := by
        rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hsq : E ^ 2 ≤ (N * ∑ i, e i) ^ 2 :=
    (sq_le_sq₀ hE (mul_nonneg hN hs)).mpr hEbound
  have hcs : (∑ i, e i) ^ 2 ≤ N * ∑ i, e i ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) e)
  change E ^ 2 ≤ N ^ 3 * ∑ i, e i ^ 2
  calc
    E ^ 2 ≤ N ^ 2 * (∑ i, e i) ^ 2 := by simpa [mul_pow] using hsq
    _ ≤ N ^ 2 * (N * ∑ i, e i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg N)
    _ = N ^ 3 * ∑ i, e i ^ 2 := by ring

theorem fourth_sum_le_card_cube {I : Type*} [Fintype I] (a : I → ℝ) :
    (∑ i, a i) ^ 4 ≤ (Fintype.card I : ℝ) ^ 3 * ∑ i, a i ^ 4 := by
  have h := energy_sum_sq_le_card_cube (Ω := Unit) (fun i _ => a i)
  simpa [← pow_mul] using h

theorem average_fourth_sum_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
  calc
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
        𝔼 n, (Fintype.card I : ℝ) ^ 3 * ∑ i, g i n ^ 4 :=
      Finset.expect_le_expect fun n _ => fourth_sum_le_card_cube (fun i => g i n)
    _ = (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem compressFrequency_eq_compress (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : Restriction.compressFrequency A B Y = compress Y A B := by
  ext x
  rfl

theorem nested_projector_restriction_apply
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (P : (F →ₗ[F2] E) → Prop) (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F)
    (S : MatrixRestrictions.Parameter A B) (N : MatrixRestrictions.Parameter C D) :
    MatrixRestrictions.restrict
      (spectralProjector Q (MatrixRestrictions.restrict (spectralProjector P f) A B T))
      C D S N =
    spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
      (T + MatrixRestrictions.embed A B S + RestrictionTransport.nestedEmbedding A B C D N) := by
  classical
  rw [OperatorPartitions.spectralProjector_restriction_projector]
  let g := spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
  change g (T + (MatrixRestrictions.embedding A B)
      (S + MatrixRestrictions.embed C D N)) =
    g ((T + (MatrixRestrictions.embedding A B) S) +
      (MatrixRestrictions.embedding A B) (MatrixRestrictions.embed C D N))
  rw [map_add, add_assoc]

theorem a5_outer_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5OuterMask X A B) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let C := A.map X.range.mkQ
  let D := B.comap X.ker.subtype
  let g := spectralProjector (a5OuterMask X A B) f
  let t := MatrixRestrictions.embed X.range X.ker S
  have hp (N : MatrixRestrictions.Parameter C D) :
      hybridDerivative C D S (mapDerivative X f) N =
        g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) := by
    have hm : (fun Y => RankBelow X Y ∧ Hybrid (compress Y X.range X.ker) C D) =
        a5OuterMask X A B := rfl
    have hh := nested_projector_restriction_apply X.range X.ker C D
      (fun Y => RankBelow X Y) (fun Y => Hybrid Y C D) f 0 S N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [hybridDerivative, hybridProjector, mapDerivative, rankProjector,
      g, t, zero_add] using hh
  calc
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have ha : C.comap X.range.mkQ = A := by
        dsimp only [C]
        rw [Submodule.comap_map_mkQ, sup_of_le_right hI]
      have hb : D.map X.ker.subtype = B := by
        dsimp only [D]
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hB]
      have hrange : (RestrictionTransport.nestedEmbedding X.range X.ker C D).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq, ha, hb]
      have htransport := RestrictionTransport.restriction_secondMoment_eq_of_same_range
        (K := F2) (P := MatrixRestrictions.Parameter C D)
        (Q := MatrixRestrictions.Parameter A B) (G := E →ₗ[F2] F)
        (RestrictionTransport.nestedEmbedding X.range X.ker C D)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
        (MatrixRestrictions.embed_injective A B) hrange g t
      simpa only [MatrixRestrictions.embedding, LinearMap.coe_mk, AddHom.coe_mk] using htransport

theorem a5_summand_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
      (hybridDerivative i.val.1 i.val.2
        (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5Mask X A B i) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let A0 := i.val.1
  let B0 := i.val.2
  let Z := compress X A0 B0
  let g := spectralProjector (a5Mask X A B i) f
  let t := MatrixRestrictions.embed X.range X.ker S
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  have hz : MatrixRestrictions.embed A0 B0
      (0 : MatrixRestrictions.Parameter A0 B0) = 0 :=
    (MatrixRestrictions.embedding A0 B0).map_zero
  have hp (N : MatrixRestrictions.Parameter Z.range Z.ker) :
      mapDerivative Z (hybridDerivative A0 B0 t f) N =
        g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) := by
    have hm : (fun Y => Hybrid Y A0 B0 ∧ RankBelow Z (compress Y A0 B0)) =
        a5Mask X A B i := rfl
    have hh := nested_projector_restriction_apply A0 B0 Z.range Z.ker
      (fun Y => Hybrid Y A0 B0) (fun Y => RankBelow Z Y) f t 0 N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [mapDerivative, rankProjector, hybridDerivative, hybridProjector,
      g, hz, add_zero] using hh
  calc
    (𝔼 N, mapDerivative Z (hybridDerivative A0 B0 t f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have hrange : (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq,
          a5_effective_annihilator X A0 A B0 hA hcover,
          a5_effective_codomain X A0 B B0 hdis hmeet]
      have htransport := RestrictionTransport.restriction_secondMoment_eq_of_same_range
        (K := F2) (P := MatrixRestrictions.Parameter Z.range Z.ker)
        (Q := MatrixRestrictions.Parameter A B) (G := E →ₗ[F2] F)
        (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embed_injective A B) hrange g t
      simpa only [MatrixRestrictions.embedding, LinearMap.coe_mk, AddHom.coe_mk] using htransport

theorem a5_energySquare_le (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)]
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) ^ 2 ≤
    (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
      ∑ i : A5GeometricIndex X A B,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2
            (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2 := by
  classical
  let J := A5GeometricIndex X A B
  let t := MatrixRestrictions.embed X.range X.ker S
  let g : J → MatrixRestrictions.Parameter A B → ℝ := fun i M =>
    spectralProjector (a5Mask X A B i) f (t + MatrixRestrictions.embed A B M)
  have hp (M : MatrixRestrictions.Parameter A B) :
      spectralProjector (a5OuterMask X A B) f
        (t + MatrixRestrictions.embed A B M) = ∑ i : J, g i M := by
    have h := congrFun (a5_projector_partition X A B hI hB f)
      (t + MatrixRestrictions.embed A B M)
    simpa only [Finset.sum_apply, g] using h
  have ho :
      (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
        S (mapDerivative X f) N ^ 2) = 𝔼 M, (∑ i : J, g i M) ^ 2 := by
    rw [a5_outer_energy X A B hI hB f S]
    exact Finset.expect_congr rfl fun M _ => congrArg (fun r : ℝ => r ^ 2) (hp M)
  have hi (i : J) :
      (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
        (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) = 𝔼 M, g i M ^ 2 :=
    a5_summand_energy X A B i f S
  rw [ho]
  calc
    (𝔼 M, (∑ i : J, g i M) ^ 2) ^ 2 ≤
        (Fintype.card J : ℝ) ^ 3 * ∑ i : J, (𝔼 M, g i M ^ 2) ^ 2 :=
      energy_sum_sq_le_card_cube g
    _ = (Fintype.card J : ℝ) ^ 3 * ∑ i : J,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) ^ 2 := by
      apply congrArg (fun r : ℝ => (Fintype.card J : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => r ^ 2) (hi i).symm

theorem map_hybrid_fourth_average
    (A0 : Submodule F2 E) (B0 : Submodule F2 F)
    (X : B0 →ₗ[F2] (E ⧸ A0)) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A0 B0 T f) N ^ 4) =
    𝔼 M, spectralProjector
      (fun Y => Hybrid Y A0 B0 ∧ RankBelow X (compress Y A0 B0)) f M ^ 4 := by
  classical
  have hp :
      spectralProjector (fun Y => RankBelow X (Restriction.compressFrequency A0 B0 Y))
        (hybridProjector A0 B0 f) =
      spectralProjector (fun Y => Hybrid Y A0 B0 ∧
        RankBelow X (Restriction.compressFrequency A0 B0 Y)) f := by
    rw [hybridProjector, spectralProjector_comp]
    congr 1
    funext Y
    exact propext and_comm
  have h := Derivatives.spectralProjector_restriction_moment_average A0 B0
    (fun Z => RankBelow X Z) (hybridProjector A0 B0 f)
    (MatrixRestrictions.embed X.range X.ker) 4
  rw [hp] at h
  simpa only [mapDerivative, rankProjector, hybridDerivative,
    MatrixRestrictions.restrict, MatrixRestrictions.translate, zero_add,
    compressFrequency_eq_compress] using h

theorem a4_fourth_average_le (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
      ∑ i : A4GeometricIndex A B,
        𝔼 T, 𝔼 N, mapDerivative i.val.2.2
          (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
  classical
  rw [a4_projector_partition A B f]
  simp only [Finset.sum_apply]
  calc
    (𝔼 M, (∑ i : A4GeometricIndex A B,
        spectralProjector (a4Mask A B i) f M) ^ 4) ≤
      (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B, 𝔼 M,
          spectralProjector (a4Mask A B i) f M ^ 4 :=
      average_fourth_sum_le_card_cube
        (fun (i : A4GeometricIndex A B) M => spectralProjector (a4Mask A B i) f M)
    _ = (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B,
          𝔼 T, 𝔼 N, mapDerivative i.val.2.2
            (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
      apply congrArg (fun r : ℝ =>
        (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      change (𝔼 M, spectralProjector
        (fun Y => Hybrid Y i.val.1 i.val.2.1 ∧
          RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)) f M ^ 4) = _
      exact (map_hybrid_fourth_average i.val.1 i.val.2.1 i.val.2.2 f).symm

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

/-- The exponent comparison after retaining the total degree loss. -/
theorem exponent_le (d i j t : ℕ) (hi : i ≤ t) (hj : j ≤ t) (ht : t ≤ d) :
    7 * d * (i + j) + 3 * i * j ≤ 24 * d * t := by
  have hs : i + j ≤ 2 * t := by omega
  have hp : i * j ≤ d * t :=
    (Nat.mul_le_mul hi hj).trans (Nat.mul_le_mul_right t ht)
  have hfirst := Nat.mul_le_mul_left (7 * d) hs
  have hsecond := Nat.mul_le_mul_left 3 hp
  have hdt : 0 ≤ d * t := Nat.zero_le _
  nlinarith

/-- Degree-forced zero moments allow the same weight bound on every raw triple. -/
theorem weighted_moment_le (d i j t : ℕ) (e : ℝ)
    (hi : i ≤ t) (hj : j ≤ t) (he : 0 ≤ e) (hz : d < t → e = 0) :
    (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) * e ≤
      (2 : ℝ) ^ (24 * d * t) * e := by
  by_cases ht : t ≤ d
  · have hn := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (exponent_le d i j t hi hj ht)
    have hr : (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) ≤
        (2 : ℝ) ^ (24 * d * t) := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_right hr he
  · rw [hz (Nat.lt_of_not_ge ht)]
    simp

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

/-- The actual averaged fourth moment attached to a raw derivative triple. -/
def tripleMoment (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 T, 𝔼 N, mapDerivative p.2.2 (hybridDerivative p.1 p.2.1 T f) N ^ 4

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleMoment_nonneg (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleMoment p f := by
  apply Finset.expect_nonneg
  intro T _
  apply Finset.expect_nonneg
  intro N _
  positivity

/-- A.4's native fourth-moment bound with its proved binary index count. -/
theorem weak_fourth_le_counted (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
        ∑ p : A4GeometricIndex A B, tripleMoment p.val f := by
  have hnat := Nat.pow_le_pow_left (A4IndexCount.card_index_le A B) 3
  rw [Nat.card_eq_fintype_card, ← pow_mul] at hnat
  have he : (Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * 3 =
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B) := by ring
  rw [he] at hnat
  have hc : (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) := by
    exact_mod_cast hnat
  have hn : 0 ≤ ∑ p : A4GeometricIndex A B, tripleMoment p.val f :=
    Finset.sum_nonneg fun p _ => tripleMoment_nonneg p.val f
  exact (OperatorNorm.a4_fourth_average_le A B f).trans
    (mul_le_mul_of_nonneg_right hc hn)

/-- Expand one original weak-pair term, retaining its original dimensions. -/
theorem weighted_weak_fourth_le_counted (d : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
      (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    ∑ p : A4GeometricIndex A B,
      (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
        3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f := by
  calc
    _ ≤ (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
        ((2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
          ∑ p : A4GeometricIndex A B, tripleMoment p.val f) :=
      mul_le_mul_of_nonneg_left (weak_fourth_le_counted A B f) (by positivity)
    _ = _ := by simp only [pow_add, Finset.mul_sum, mul_assoc]

theorem tripleMoment_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleMoment p f = 0 :=
  DerivativeDegree.map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    p.1 p.2.1 p.2.2 f hf h

/-- The weight after relabeling the actual raw derivative triple. -/
def tripleTerm (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  (2 : ℝ) ^ (24 * d * A13Index.size p) * tripleMoment p f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleTerm_nonneg (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleTerm d p f :=
  mul_nonneg (by positivity) (tripleMoment_nonneg p f)

theorem tripleTerm_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleTerm d p f = 0 := by
  unfold tripleTerm
  rw [tripleMoment_eq_zero_of_lt_size p f hf h, mul_zero]

theorem weighted_geometric_moment_le {d : ℕ}
    (A : Submodule F2 E) (B : Submodule F2 F)
    (p : A4GeometricIndex A B) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f ≤
      tripleTerm d p.val f := by
  have hi : Module.finrank F2 A ≤ A13Index.size p.val := by
    have h := A13Index.dim_weakA p
    unfold A13Index.size MatrixRestrictions.order
    omega
  have hj : Module.finrank F2 (F ⧸ B) ≤ A13Index.size p.val := by
    have h := A13Index.codim_weakB p
    unfold A13Index.size MatrixRestrictions.order
    omega
  exact weighted_moment_le d _ _ _ _ hi hj (tripleMoment_nonneg p.val f)
    (fun h => tripleMoment_eq_zero_of_lt_size p.val f hf h)

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- The displayed A.13 sum: its original positive total order is retained. -/
def positiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.PositiveTriple (E := E) (F := F), tripleTerm d p.val f

/-- The same sum after the genuine degree-support cutoff. -/
def boundedPositiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d, tripleTerm d p.val f

/-- Apply A.4 and its count, then forget the uniquely reconstructible weak pair.
The old nonzero condition is carried by `positiveMap`; no descendant condition
is substituted for it. -/
theorem weakFourthSum_le_positiveTripleSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    A1Reduction.weakFourthSum d f ≤ positiveTripleSum d f := by
  classical
  have heq : A1Reduction.weakFourthSum d f =
      ∑ p : A13Index.WeakPositive (E := E) (F := F),
        (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.val.1 +
          Module.finrank F2 (F ⧸ p.val.2))) *
          (𝔼 M, spectralProjector
            (fun Y => p.val.1 ≤ Y.range ∧ Y.ker ≤ p.val.2) f M ^ 4) := by
    symm
    exact F1Gram.sum_subtype_eq
      (fun p : Submodule F2 E × Submodule F2 F => p ≠ (⊥, ⊤))
      (fun p => (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.1 +
        Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M ^ 4))
  rw [heq]
  calc
    _ ≤ ∑ p : A13Index.WeakPositive (E := E) (F := F),
        ∑ q : A4GeometricIndex p.val.1 p.val.2, tripleTerm d q.val f := by
      apply Finset.sum_le_sum
      intro p _
      exact (weighted_weak_fourth_le_counted d p.val.1 p.val.2 f).trans
        (Finset.sum_le_sum fun q _ => weighted_geometric_moment_le p.val.1 p.val.2 q f hf)
    _ = ∑ w : A13Index.PositiveWitness (E := E) (F := F),
        tripleTerm d w.2.val f := by
      simp only [Fintype.sum_sigma]
    _ ≤ positiveTripleSum d f :=
      F1Gram.sum_comp_le A13Index.positiveMap A13Index.positiveMap_injective
        (fun q : A13Index.PositiveTriple (E := E) (F := F) => tripleTerm d q.val f)
        (fun q => tripleTerm_nonneg d q.val f)

theorem positiveTripleSum_eq_bounded (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    positiveTripleSum d f = boundedPositiveTripleSum d f := by
  classical
  unfold positiveTripleSum boundedPositiveTripleSum
  rw [F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) => 0 < A13Index.size p)
      (fun p => tripleTerm d p f),
    F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) =>
        0 < A13Index.size p ∧ A13Index.size p ≤ d)
      (fun p => tripleTerm d p f)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < A13Index.size p
  · by_cases ht : A13Index.size p ≤ d
    · rw [ite_eq_left hp, ite_eq_left ⟨hp, ht⟩]
    · rw [ite_eq_left hp, ite_eq_right (fun h => ht h.2)]
      exact tripleTerm_eq_zero_of_lt_size p f hf (Nat.lt_of_not_ge ht)
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

/-- Equation A.13 with the literal positive-triple sum. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + positiveTripleSum d f := by
  have hbase := A1Reduction.degree_reduction f d (fun Y hY => hf Y hY)
  exact hbase.trans (add_le_add le_rfl (weakFourthSum_le_positiveTripleSum f d hf))

/-- Equation A.13 after removing terms whose actual derivative is zero. -/
theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  simpa only [positiveTripleSum_eq_bounded f d hf] using degree_reduction f d hf

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

section

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.NaturalTransport
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

local instance hybridCompositionQuotientFinite {V : Type*}
    [AddCommGroup V] [Module F2 V] [Finite V]
    (P : Submodule F2 V) : Finite (V ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance hybridCompositionCompressedDualFintype {U V : Type*}
    [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V]
    (A : Submodule F2 U) (B : Submodule F2 V) : Fintype (B →ₗ[F2] (U ⧸ A)) :=
  OperatorNorm.compressedDualFintype A B

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rank_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F') (L : E →ₗ[F2] F) :
    Module.finrank F2 (LinearEquiv.arrowCongr a b L).range =
      Module.finrank F2 L.range := by
  have hh : LinearEquiv.arrowCongr a b L =
      (b.toLinearMap.comp L).comp a.symm.toLinearMap := by
    ext x
    rfl
  rw [hh, LinearEquiv.range_comp, LinearMap.range_comp]
  exact b.finrank_map_eq L.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rankBelow_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (X Y : F →ₗ[F2] E) :
    RankBelow (LinearEquiv.arrowCongr b a X) (LinearEquiv.arrowCongr b a Y) ↔
      RankBelow X Y := by
  unfold RankBelow
  rw [← map_sub, rank_arrowCongr, rank_arrowCongr, rank_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem trace_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTracePair (LinearEquiv.arrowCongr a b M) (LinearEquiv.arrowCongr b a Z) =
      linearTracePair M Z := by
  unfold linearTracePair
  rw [← LinearEquiv.arrowCongr_comp]
  exact LinearMap.trace_conj' (M.comp Z) b

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem character_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTraceCharacter (LinearEquiv.arrowCongr b a Z) (LinearEquiv.arrowCongr a b M) =
      linearTraceCharacter Z M := by
  simp only [linearTraceCharacter_apply, trace_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem admissible_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) (M : E →ₗ[F2] F) :
    ((LinearEquiv.arrowCongr b a Z).range ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ (LinearEquiv.arrowCongr b a Z).ker) ↔
    (Z.range ≤ M.ker ∧ M.range ≤ Z.ker) := by
  simp [LinearMap.range_le_ker_iff, ← LinearEquiv.arrowCongr_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem derivative_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker)).range =
      (embedding (LinearEquiv.arrowCongr b a Z).range
        (LinearEquiv.arrowCongr b a Z).ker).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  let Z' := LinearEquiv.arrowCongr b a Z
  ext M'
  change (∃ N, e (embed Z.range Z.ker N) = M') ↔
    (∃ N, embed Z'.range Z'.ker N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff Z'.range Z'.ker _).mpr
    apply (admissible_arrowCongr a b Z (embed Z.range Z.ker N)).mpr
    exact (exists_embed_iff Z.range Z.ker _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff Z'.range Z'.ker M').mp hM'
    have hm : Z.range ≤ M.ker ∧ M.range ≤ Z.ker := by
      apply (admissible_arrowCongr a b Z M).mp
      change Z'.range ≤ (e M).ker ∧ (e M).range ≤ Z'.ker
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff Z.range Z.ker M).mpr hm
    refine ⟨N, ?_⟩
    rw [hN]
    exact he

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem linearCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    linearCoeff (fun M => f (LinearEquiv.arrowCongr a b M)) Z =
      linearCoeff f (LinearEquiv.arrowCongr b a Z) := by
  unfold linearCoeff
  exact Fintype.expect_equiv (LinearEquiv.arrowCongr a b).toEquiv _ _
    (fun M => by
      change f (LinearEquiv.arrowCongr a b M) * (linearTraceCharacter Z M).re =
        f (LinearEquiv.arrowCongr a b M) *
          (linearTraceCharacter (LinearEquiv.arrowCongr b a Z)
            (LinearEquiv.arrowCongr a b M)).re
      rw [character_arrowCongr])

theorem rankProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    rankProjector Z (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankProjector, linearCoeff_spectralProjector,
    linearCoeff_pullback, rankBelow_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

theorem mapDerivative_energy_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    (𝔼 N, mapDerivative Z (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, mapDerivative (LinearEquiv.arrowCongr b a Z) f N ^ 2 := by
  simp only [mapDerivative, restrict,
    UniqueGamesTheorem.Fourier.MatrixRestrictions.translate, zero_add]
  rw [rankProjector_pullback]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker))
    (embedding (LinearEquiv.arrowCongr b a Z).range (LinearEquiv.arrowCongr b a Z).ker)
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective Z.range Z.ker))
    (embed_injective _ _) (derivative_embedding_range a b Z)
    (fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f M ^ 2)

end General

section Nested
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def quotientFactor (A : Submodule F2 E) (C : Submodule F2 (E ⧸ A)) :
    (E ⧸ C.comap A.mkQ) ≃ₗ[F2] ((E ⧸ A) ⧸ C) :=
  (Submodule.quotEquivOfEq (C.comap A.mkQ) (C.mkQ.comp A.mkQ).ker
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
      ((C.mkQ.comp A.mkQ).quotKerEquivOfSurjective
        (C.mkQ_surjective.comp A.mkQ_surjective))

omit [FiniteDimensional F2 E] [Finite E] in
@[simp] theorem quotientFactor_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) (x : E) :
    quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x) := by
  simp [quotientFactor]

def outputFactor (B : Submodule F2 F) (D : Submodule F2 B) :
    D ≃ₗ[F2] (D.map B.subtype) :=
  Submodule.equivMapOfInjective B.subtype Subtype.val_injective D

omit [FiniteDimensional F2 F] [Finite F] in
@[simp] theorem outputFactor_val (B : Submodule F2 F) (D : Submodule F2 B) (x : D) :
    ((outputFactor B D x : D.map B.subtype) : F) = ((x : B) : F) := rfl

def parameterFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D ≃ₗ[F2] Parameter (C.comap A.mkQ) (D.map B.subtype) :=
  LinearEquiv.arrowCongr (quotientFactor A C).symm (outputFactor B D)

def dualFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (D →ₗ[F2] ((E ⧸ A) ⧸ C)) ≃ₗ[F2]
      ((D.map B.subtype) →ₗ[F2] (E ⧸ C.comap A.mkQ)) :=
  LinearEquiv.arrowCongr (outputFactor B D) (quotientFactor A C).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dualFactor_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    Module.finrank F2 (dualFactor A B C D Z).range = Module.finrank F2 Z.range :=
  rank_arrowCongr (outputFactor B D) (quotientFactor A C).symm Z

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem parameterFactor_embedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (N : Parameter C D) :
    embed (C.comap A.mkQ) (D.map B.subtype) (parameterFactor A B C D N) =
      RestrictionTransport.nestedEmbedding A B C D N := by
  ext x
  change ((outputFactor B D (N (quotientFactor A C ((C.comap A.mkQ).mkQ x)))) : F) =
    ((N (C.mkQ (A.mkQ x)) : B) : F)
  rw [quotientFactor_mkQ]
  rfl

theorem nested_hybridDerivative_function
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B) :
    hybridDerivative C D S (hybridDerivative A B T f) =
      fun N => hybridDerivative (C.comap A.mkQ) (D.map B.subtype)
        (T + embed A B S) f (parameterFactor A B C D N) := by
  funext N
  have hh := OperatorNorm.nested_projector_restriction_apply A B C D
    (fun Y => LinearIdentities.Hybrid Y A B)
    (fun Z => LinearIdentities.Hybrid Z C D) f T S N
  have hp : (fun Y => LinearIdentities.Hybrid Y A B ∧
        LinearIdentities.Hybrid (Restriction.compressFrequency A B Y) C D) =
      (fun Y => LinearIdentities.Hybrid Y (C.comap A.mkQ) (D.map B.subtype)) := by
    funext Y
    exact propext (HybridComposition.effective_hybrid_iff A B C D Y)
  rw [hp] at hh
  change _ = hybridProjector (C.comap A.mkQ) (D.map B.subtype) f
    ((T + embed A B S) + embed (C.comap A.mkQ) (D.map B.subtype)
      (parameterFactor A B C D N))
  rw [parameterFactor_embedding]
  exact hh

theorem nested_mapDerivative_energy
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    (𝔼 N, mapDerivative Z (hybridDerivative C D S (hybridDerivative A B T f)) N ^ 2) =
      𝔼 N, mapDerivative (dualFactor A B C D Z)
        (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) N ^ 2 := by
  rw [nested_hybridDerivative_function]
  exact mapDerivative_energy_pullback (quotientFactor A C).symm (outputFactor B D)
    (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) Z

theorem nested_mapDerivative_energySquare_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    (𝔼 T, 𝔼 S, (𝔼 N,
      mapDerivative Z (hybridDerivative C D S (hybridDerivative A B T f)) N ^ 2)^2) =
    𝔼 U, (𝔼 N, mapDerivative (dualFactor A B C D Z)
      (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) U f) N ^ 2)^2 := by
  simp_rw [nested_mapDerivative_energy A B C D f]
  exact Restriction.real_translation_average (embed A B)
    (fun U => (𝔼 N, mapDerivative (dualFactor A B C D Z)
      (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) U f) N ^ 2)^2)

end Nested
end UniqueGamesTheorem.Appendix.NaturalTransport

end

end

end OAI

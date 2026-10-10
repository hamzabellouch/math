import Mathlib
import OAI.Computability.MaxCut.Games.A4IndexCount

namespace OAI

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

namespace MaxCutGames.Appendix.OperatorNorm

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
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
      have range_eq : (RestrictionTransport.nestedEmbedding X.range X.ker C D).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq, ha, hb]
      let equiv := RestrictionTransport.sameRangeEquiv
        (K := F2) (G := E →ₗ[F2] F)
        (P := MatrixRestrictions.Parameter C D) (Q := MatrixRestrictions.Parameter A B)
        (RestrictionTransport.nestedEmbedding X.range X.ker C D)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
        (MatrixRestrictions.embed_injective A B) range_eq
      apply Fintype.expect_equiv equiv.toEquiv
      intro parameter
      exact congrArg (fun value => g (t + value) ^ 2)
        (RestrictionTransport.sameRangeEquiv_commutes
          (K := F2) (G := E →ₗ[F2] F)
          (P := MatrixRestrictions.Parameter C D) (Q := MatrixRestrictions.Parameter A B)
          (RestrictionTransport.nestedEmbedding X.range X.ker C D)
          (MatrixRestrictions.embedding A B)
          (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
          (MatrixRestrictions.embed_injective A B) range_eq parameter).symm

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
      have range_eq : (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq,
          a5_effective_annihilator X A0 A B0 hA hcover,
          a5_effective_codomain X A0 B B0 hdis hmeet]
      let equiv := RestrictionTransport.sameRangeEquiv
        (K := F2) (G := E →ₗ[F2] F)
        (P := MatrixRestrictions.Parameter Z.range Z.ker) (Q := MatrixRestrictions.Parameter A B)
        (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embed_injective A B) range_eq
      apply Fintype.expect_equiv equiv.toEquiv
      intro parameter
      exact congrArg (fun value => g (t + value) ^ 2)
        (RestrictionTransport.sameRangeEquiv_commutes
          (K := F2) (G := E →ₗ[F2] F)
          (P := MatrixRestrictions.Parameter Z.range Z.ker) (Q := MatrixRestrictions.Parameter A B)
          (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
          (MatrixRestrictions.embedding A B)
          (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
          (MatrixRestrictions.embed_injective A B) range_eq parameter).symm

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

end MaxCutGames.Appendix.OperatorNorm
end

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace MaxCutGames.Appendix.NaturalTransport
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

local instance {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (P : Submodule F2 V) : Finite (V ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance {U V : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V]
    (A : Submodule F2 U) (B : Submodule F2 V) : Fintype (B →ₗ[F2] (U ⧸ A)) :=
  OperatorNorm.compressedDualFintype A B

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rank_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F') (L : E →ₗ[F2] F) :
    Module.finrank F2 (LinearEquiv.arrowCongr a b L).range =
      Module.finrank F2 L.range := by
  have hh : LinearEquiv.arrowCongr a b L =
      (b.toLinearMap.comp L).comp a.symm.toLinearMap := by
    ext x
    rfl
  rw [hh, LinearEquiv.range_comp, LinearMap.range_comp]
  exact b.finrank_map_eq L.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rankBelow_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (X Y : F →ₗ[F2] E) :
    RankBelow (LinearEquiv.arrowCongr b a X) (LinearEquiv.arrowCongr b a Y) ↔
      RankBelow X Y := by
  unfold RankBelow
  rw [← map_sub, rank_arrowCongr, rank_arrowCongr, rank_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem trace_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTracePair (LinearEquiv.arrowCongr a b M) (LinearEquiv.arrowCongr b a Z) =
      linearTracePair M Z := by
  unfold linearTracePair
  rw [← LinearEquiv.arrowCongr_comp]
  exact LinearMap.trace_conj' (M.comp Z) b

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem character_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTraceCharacter (LinearEquiv.arrowCongr b a Z) (LinearEquiv.arrowCongr a b M) =
      linearTraceCharacter Z M := by
  simp only [linearTraceCharacter_apply, trace_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem admissible_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) (M : E →ₗ[F2] F) :
    ((LinearEquiv.arrowCongr b a Z).range ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ (LinearEquiv.arrowCongr b a Z).ker) ↔
    (Z.range ≤ M.ker ∧ M.range ≤ Z.ker) := by
  simp [LinearMap.range_le_ker_iff, ← LinearEquiv.arrowCongr_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
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
  simp only [mapDerivative, restrict, MaxCutGames.Fourier.MatrixRestrictions.translate, zero_add]
  rw [rankProjector_pullback]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker))
    (embedding (LinearEquiv.arrowCongr b a Z).range (LinearEquiv.arrowCongr b a Z).ker)
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective Z.range Z.ker))
    (embed_injective _ _) (derivative_embedding_range a b Z)
    (fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f M ^ 2)

end General

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

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem dualFactor_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    Module.finrank F2 (dualFactor A B C D Z).range = Module.finrank F2 Z.range :=
  rank_arrowCongr (outputFactor B D) (quotientFactor A C).symm Z

omit [FiniteDimensional F2 F] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] [Finite E] in
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

end MaxCutGames.Appendix.NaturalTransport

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine MaxCutGames.Fourier.MatrixRestrictions.translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic

variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']

private theorem mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport (a : E ≃ₗ[F2] E')
    (A : Submodule F2 E) (x : E) :
    a x ∈ A.map a.toLinearMap ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp h
    exact (a.injective heq) ▸ hy
  · intro h
    exact Submodule.mem_map.mpr ⟨x, h, rfl⟩

/-- The two clauses of the actual Hybrid selector are coordinate invariant. -/
theorem hybrid_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (S : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F) :
    LinearIdentities.Hybrid (LinearEquiv.arrowCongr b a S)
      (A.map a.toLinearMap) (B.map b.toLinearMap) ↔
      LinearIdentities.Hybrid S A B := by
  constructor
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := hr ((mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A x).mpr hx)
      refine ⟨b.symm y, a.injective hy⟩
    · intro y hy
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B y).mp
      apply hk
      change (LinearEquiv.arrowCongr b a S) (b y) ∈ A.map a.toLinearMap
      simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
        using (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A (S y)).mpr hy
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨z, hz⟩ := hr hy
      refine ⟨b z, ?_⟩
      change a (S (b.symm (b z))) = a y
      rw [b.symm_apply_apply]
      exact congrArg a hz
    · intro y hy
      have hy' : S (b.symm y) ∈ A := (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A _).mp hy
      have hm := (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mpr (hk hy')
      simpa only [LinearEquiv.apply_symm_apply] using hm

/-- The actual vanishing and range constraints of an affine perturbation
transport to the mapped subspaces. -/
theorem restriction_admissible_arrowCongr
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (A : Submodule F2 E) (B : Submodule F2 F) :
    (A.map a.toLinearMap ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ B.map b.toLinearMap) ↔
      (A ≤ M.ker ∧ M.range ≤ B) := by
  constructor
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      have heq := hk ((mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A x).mpr hx)
      have heq' : b (M x) = b 0 := by
        simpa only [LinearMap.mem_ker, LinearEquiv.arrowCongr_apply,
          LinearEquiv.symm_apply_apply, map_zero] using heq
      exact b.injective heq'
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mp
      apply hr
      exact ⟨a x, by simp only [LinearEquiv.arrowCongr_apply,
        LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      change b (M (a.symm (a y))) = 0
      rw [a.symm_apply_apply, hk hy, map_zero]
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mpr
      exact hr ⟨a.symm x, rfl⟩

/-- Transported quotient parameters give exactly the directly transported
affine perturbations; no multiplicity or normalization factor occurs. -/
theorem hybrid_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (A : Submodule F2 E) (B : Submodule F2 F) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B)).range =
      (embedding (A.map a.toLinearMap) (B.map b.toLinearMap)).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  ext M'
  change (∃ N, e (embed A B N) = M') ↔
    (∃ N, embed (A.map a.toLinearMap) (B.map b.toLinearMap) N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff _ _ _).mpr
    apply (restriction_admissible_arrowCongr a b (embed A B N) A B).mpr
    exact (exists_embed_iff A B _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff _ _ _).mp hM'
    have hm : A ≤ M.ker ∧ M.range ≤ B := by
      apply (restriction_admissible_arrowCongr a b M A B).mp
      change A.map a.toLinearMap ≤ (e M).ker ∧
        (e M).range ≤ B.map b.toLinearMap
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr hm
    exact ⟨N, by rw [hN]; exact he⟩

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

/-- The actual Fourier Hybrid projector commutes with coordinate pullback. -/
theorem hybridProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F) :
    hybridProjector A B (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [hybridProjector, linearCoeff_spectralProjector,
    NaturalTransport.linearCoeff_pullback, hybrid_arrowCongr]

/-- The actual pure-rank Fourier component commutes with coordinate pullback. -/
theorem rankComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ) :
    rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankComponent i f (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankComponent, coeff_component,
    NaturalTransport.linearCoeff_pullback, NaturalTransport.rank_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

/-- Exact normalized energy transport, with the actual Hybrid selector,
quotient restriction, and affine MaxCutGames.Fourier.MatrixRestrictions.translate transported together. -/
theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, MaxCutGames.Fourier.MatrixRestrictions.translate, hybridProjector_pullback, map_add]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B))
    (embedding (A.map a.toLinearMap) (B.map b.toLinearMap))
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective A B))
    (embed_injective _ _) (hybrid_embedding_range a b A B)
    (fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
      (LinearEquiv.arrowCongr a b T + M) ^ 2)

/-- Pure-rank derivative energy is invariant under both coordinate changes. -/
theorem hybridDerivative_rankComponent_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M))) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) (rankComponent i f) N ^ 2 := by
  rw [rankComponent_pullback]
  exact hybridDerivative_energy_pullback a b (rankComponent i f) A B T

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI

import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas

namespace OAI

section

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix.Derivatives

namespace UniqueGamesTheorem.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

private theorem indicator_eq_sum_of_unique {I : Type*} [Fintype I]
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
  exact indicator_eq_sum_of_unique (P Y) (fun i => R i Y)
    (linearCoeff f Y) (hpart Y) (fun i => hback i Y)

variable [Finite E] [Finite F]

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

abbrev A4Geometry (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Valid A B

abbrev A4GeometricIndex (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Index A B

def a4Mask (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2.1 ∧
    RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
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

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
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

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
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

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
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

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI

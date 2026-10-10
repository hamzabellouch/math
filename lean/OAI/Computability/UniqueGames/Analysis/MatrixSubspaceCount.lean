import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas

namespace OAI

section

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace UniqueGamesTheorem.Fourier.MatrixSubspaceCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section GeneralField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Taking the image of an endomorphism reaches every actual subspace. -/
theorem endomorphism_range_surjective :
    Function.Surjective (fun f : V →ₗ[K] V => LinearMap.range f) := by
  intro S
  obtain ⟨T, hT⟩ := S.exists_isCompl
  exact ⟨S.projection T hT, Submodule.range_projection hT⟩

theorem card_subspaces_le_endomorphisms [Finite V] :
    Nat.card (Submodule K V) ≤ Nat.card (V →ₗ[K] V) := by
  let : Finite (V →ₗ[K] V) := Finite.of_injective
    (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Nat.card_le_card_of_surjective _ endomorphism_range_surjective

end GeneralField

section BinaryField

variable {C : Type*} [AddCommGroup C] [Module F2 C] [Module.Finite F2 C]

private theorem finite_color_space : Finite C :=
  Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective

private theorem finite_endomorphisms : Finite (C →ₗ[F2] C) := by
  let : Finite C := finite_color_space
  exact Finite.of_injective (fun f : C →ₗ[F2] C => (f : C → C)) DFunLike.coe_injective

private theorem finite_subspaces : Finite (Submodule F2 C) := by
  let : Finite (C →ₗ[F2] C) := finite_endomorphisms
  exact Finite.of_surjective _ endomorphism_range_surjective

theorem card_binary_subspaces_le :
    Nat.card (Submodule F2 C) ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite C := finite_color_space
  calc
    _ ≤ Nat.card (C →ₗ[F2] C) := card_subspaces_le_endomorphisms
    _ = _ := UniqueGamesTheorem.Appendix.CompressionCount.natCard_linearMap

theorem card_binary_subspaces_le_of_finrank_le (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (Submodule F2 C) ≤ 2 ^ (s * s) := by
  exact card_binary_subspaces_le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs))

theorem card_admissible_subspaces_le (P : Submodule F2 C → Prop) :
    Nat.card {S : Submodule F2 C // P S} ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite (Submodule F2 C) := finite_subspaces
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    card_binary_subspaces_le

/-- Counting fixed colors together with actual admissible subspaces gives
precisely the `q * 2^(s*s)` denominator budget from (5.13). -/
theorem card_color_admissible_subspaces_le (P : Submodule F2 C → Prop) :
    Nat.card (C × {S : Submodule F2 C // P S}) ≤
      Nat.card C * 2 ^ (finrank F2 C * finrank F2 C) := by
  rw [Nat.card_prod]
  exact Nat.mul_le_mul_left _ (card_admissible_subspaces_le P)

theorem card_color_admissible_subspaces_le_of_finrank_le
    (P : Submodule F2 C → Prop) (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (C × {S : Submodule F2 C // P S}) ≤ Nat.card C * 2 ^ (s * s) := by
  exact (card_color_admissible_subspaces_le P).trans
    (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs)))

end BinaryField

end UniqueGamesTheorem.Fourier.MatrixSubspaceCount

end

end OAI

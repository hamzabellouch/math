import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Quadratic.BlockNoiseProbabilityLemmas

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual binary-linear embedding belonging to an oriented child. -/
def orientedBlockLinear (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

/-- The nonlinear-change indicator for the actual oriented quadratic block. -/
def orientedBlockChange (i : BlockOrientationIndex F) (p : Vec F × Vec F)
    (d : Vec F) : ℚ := by
  classical
  exact if blockObservable (p + orientedBlockLinear i d) ≠ blockObservable p then 1 else 0

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

/-- For one fixed field line, random orientation sends a fixed nonzero
logical difference uniformly onto that line's nonzero block perturbations. -/
theorem mean_orientations_change (A : FieldLine F) (p : Vec F × Vec F)
    (d : Vec F) (hd : d ≠ 0) :
    (𝔼 J : BlockOrientation A, orientedBlockChange ⟨A, J⟩ p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  let : Finite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A)) := DFunLike.finite _
  let := Fintype.ofFinite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A))
  calc
    _ = nonzeroBlockChangeProbability (lineGenerator A) p := by
      unfold nonzeroBlockChangeProbability orientedBlockChange
      simp only [Fintype.expect_eq_sum_div_card]
      exact OrientationVectors.mean_iso_nonzero (chosenBlockOrientation A) d hd
        (fun u => if blockObservable (p + (u.val : Vec F × Vec F)) ≠
          blockObservable p then 1 else 0)
    _ = _ := nonzeroBlockChangeProbability_eq _ (lineGenerator_ne_zero A) p

variable [Fintype (FieldLine F)] [Fintype (Vec F ≃ₗ[ZMod 2] Vec F)]

/-- Equal orientation-fiber sizes make the pair-index average exactly an
independent uniform line followed by a uniform orientation of that line. -/
theorem mean_block_pairs (f : BlockOrientationIndex F → ℚ) :
    (𝔼 i : BlockOrientationIndex F, f i) =
      𝔼 A : FieldLine F, 𝔼 J : BlockOrientation A, f ⟨A, J⟩ := by
  classical
  calc
    _ = 𝔼 z : FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F),
        f ((blockOrientationIndexEquiv (F := F)).symm z) := by
      exact Fintype.expect_equiv (blockOrientationIndexEquiv (F := F)) _ _
        (fun i => by simp)
    _ = 𝔼 A : FieldLine F, 𝔼 a : Vec F ≃ₗ[ZMod 2] Vec F,
        f ⟨A, (blockOrientationEquiv A).symm a⟩ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro A _
      exact Fintype.expect_equiv (blockOrientationEquiv A).symm _ _ (fun _ => rfl)

/-- Pointwise in the initial aggregate: the actual oriented-child average
has the exact one-level nonlinear survival rate. -/
theorem mean_oriented_block_change (p : Vec F × Vec F) (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  simp_rw [mean_orientations_change _ p d hd]
  exact Fintype.expect_const _

/-- The averaged block kernel required by the parent-noise recurrence,
now proved for the concrete quadratic construction. -/
theorem mean_oriented_block_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [Finset.expect_comm]
  simp_rw [mean_oriented_block_change _ d hd]
  exact Fintype.expect_const _

end UniqueGamesTheorem.Gadget.OrientedBlockKernel

end

end

end OAI

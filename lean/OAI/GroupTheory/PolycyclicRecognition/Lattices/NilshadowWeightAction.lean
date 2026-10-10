import OAI.GroupTheory.PolycyclicRecognition.Lattices.CartanNilshadow

namespace OAI

/-! # The original solvable algebra as an extension of its nilshadow -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "σ" => heightSemisimpleAction T H
local notation "e" => cartanNilshadowEquiv T H

theorem heightSemisimpleAction_apply_commute (x y z : L) : σ x (σ y z) = σ y (σ x z) := by
  have h := DFunLike.congr_fun (heightSemisimpleAction_commute T H x y) z
  exact sub_eq_zero.mp h

theorem cartanNilshadow_bracket_symm (p q : K) :
    (e).symm ⁅p, q⁆ = ⁅(e).symm p, (e).symm q⁆ - σ ((e).symm p) ((e).symm q) +
      σ ((e).symm q) ((e).symm p) := by
  obtain ⟨x, rfl⟩ := (e).surjective p
  obtain ⟨y, rfl⟩ := (e).surjective q
  simpa only [LinearEquiv.symm_apply_apply] using cartanNilshadow_bracket T H x y

theorem semisimple_derives_nilshadow_bracket (x y z : L) :
    σ x (⁅y, z⁆ - σ y z + σ z y) =
      (⁅y, σ x z⁆ - σ y (σ x z) + σ (σ x z) y) +
      (⁅σ x y, z⁆ - σ (σ x y) z + σ z (σ x y)) := by
  simp only [map_add, map_sub, LieDerivation.apply_lie_eq_add,
    heightSemisimpleAction_annihilate, LieDerivation.zero_apply, sub_zero, add_zero]
  rw [heightSemisimpleAction_apply_commute T H x y z,
    heightSemisimpleAction_apply_commute T H x z y]
  abel

def nilshadowWeightOperator (x : L) : K →ₗ[ℝ] K :=
  (e).toLinearMap.comp ((σ x).toLinearMap.comp (e).symm.toLinearMap)

@[simp]
theorem nilshadowWeightOperator_symm (x : L) (p : K) :
    (e).symm (nilshadowWeightOperator T H x p) = σ x ((e).symm p) :=
  (e).symm_apply_apply _

def nilshadowWeightDerivation (x : L) : LieDerivation ℝ K K where
  toLinearMap := nilshadowWeightOperator T H x
  leibniz' p q := by
    rw [← lie_skew q (nilshadowWeightOperator T H x p), sub_neg_eq_add]
    apply (e).symm.injective
    rw [map_add, nilshadowWeightOperator_symm, cartanNilshadow_bracket_symm,
      cartanNilshadow_bracket_symm, cartanNilshadow_bracket_symm,
      nilshadowWeightOperator_symm, nilshadowWeightOperator_symm]
    exact semisimple_derives_nilshadow_bracket T H x ((e).symm p) ((e).symm q)

@[simp]
theorem nilshadowWeightDerivation_symm (x : L) (p : K) :
    (e).symm (nilshadowWeightDerivation T H x p) = σ x ((e).symm p) :=
  nilshadowWeightOperator_symm T H x p

theorem nilshadowWeightDerivation_equiv (x y : L) :
    nilshadowWeightDerivation T H x (e y) = e (σ x y) := by
  apply (e).symm.injective
  simp only [nilshadowWeightDerivation_symm, LinearEquiv.symm_apply_apply]

def nilshadowWeightAction : L →ₗ⁅ℝ⁆ LieDerivation ℝ K K where
  toFun := nilshadowWeightDerivation T H
  map_add' x y := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.add_apply, map_add, nilshadowWeightDerivation_symm,
      LieDerivation.add_apply]
  map_smul' r x := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.smul_apply, map_smul, nilshadowWeightDerivation_symm,
      RingHom.id_apply, LieDerivation.smul_apply]
  map_lie' {x y} := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.lie_apply, map_sub, nilshadowWeightDerivation_symm,
      heightSemisimpleAction_lie, LieDerivation.zero_apply,
      heightSemisimpleAction_apply_commute T H x y, sub_self]

def nilshadowSemidirectEmbedding :
    L →ₗ⁅ℝ⁆ K ⋊⁅(nilshadowWeightAction T H).range.incl⁆ (nilshadowWeightAction T H).range where
  toFun x := ⟨e x, (nilshadowWeightAction T H).rangeRestrict x⟩
  map_add' x y := by
    apply SemiDirectSum.ext
    · exact (e).map_add x y
    · exact map_add _ _ _
  map_smul' r x := by
    apply SemiDirectSum.ext
    · exact (e).map_smul r x
    · exact map_smul _ _ _
  map_lie' {x y} := by
    apply SemiDirectSum.ext
    · apply (e).symm.injective
      change (e).symm (e ⁅x, y⁆) = (e).symm (⁅e x, e y⁆ +
        nilshadowWeightDerivation T H x (e y) - nilshadowWeightDerivation T H y (e x))
      rw [LinearEquiv.symm_apply_apply, map_sub, map_add,
        cartanNilshadow_bracket, nilshadowWeightDerivation_symm,
        nilshadowWeightDerivation_symm, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply]
      abel
    · exact LieHom.map_lie _ x y

theorem nilshadowSemidirectEmbedding_injective :
    Function.Injective (nilshadowSemidirectEmbedding T H) := by
  intro x y h
  exact (e).injective (congrArg SemiDirectSum.left h)

end PolycyclicRecognition

end

end OAI

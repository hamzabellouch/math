import Mathlib.LinearAlgebra.Dimension.Constructions
import OAI.Computability.UniqueGames.Decoding.PrivateStrategyLemmas
import OAI.Computability.UniqueGames.Inverse.RowErasureMatrixLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def domainCoordinates (k : ℕ) :
    ActualHomogeneous.E k ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ActualHomogeneous.finrank_E, Module.finrank_fin_fun])

def changeDomain {D E K : Type*} [AddCommGroup D] [Module F2 D]
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    (e : D ≃ₗ[F2] E) : (D →ₗ[F2] K) ≃ₗ[F2] (E →ₗ[F2] K) where
  toFun M := M.comp e.symm.toLinearMap
  invFun M := M.comp e.toLinearMap
  left_inv M := by ext x; simp
  right_inv M := by ext x; simp
  map_add' M N := by ext x; rfl
  map_smul' c M := by ext x; rfl

def mapEquiv (k ell : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) ≃ₗ[F2]
      Inverse.Shortcode.Mat ell (1 + 2 * k) :=
  (changeDomain (domainCoordinates k)).trans LinearMap.toMatrix'

@[simp] theorem mapEquiv_apply (k ell : ℕ)
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k ell M = LinearMap.toMatrix' (M.comp (domainCoordinates k).symm.toLinearMap) :=
  rfl

@[simp] theorem mapEquiv_symm_apply (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) :
    (mapEquiv k ell).symm M = (Matrix.toLin' M).comp (domainCoordinates k).toLinearMap :=
  rfl

def functionalEquiv (k : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] F2) ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  (changeDomain (domainCoordinates k)).trans ((Pi.basisFun F2 (Fin (1 + 2 * k))).constr F2).symm

@[simp] theorem functionalEquiv_apply (k : ℕ)
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (j : Fin (1 + 2 * k)) :
    functionalEquiv k l j = l ((domainCoordinates k).symm (Pi.single j 1)) := by
  simp [functionalEquiv, changeDomain, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

theorem mapEquiv_rankOne (k ell : ℕ) (l : ActualHomogeneous.E k →ₗ[F2] F2)
    (a : Fin ell → F2) :
    mapEquiv k ell (l.smulRight a) = Inverse.Shortcode.rankOne a (functionalEquiv k l) := by
  ext i j
  simp [Inverse.Shortcode.rankOne, mul_comm]

theorem mapEquiv_symm_add_rankOne (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k))
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (a : Fin ell → F2) :
    (mapEquiv k ell).symm (M + Inverse.Shortcode.rankOne a (functionalEquiv k l)) =
      (mapEquiv k ell).symm M + l.smulRight a := by
  apply (mapEquiv k ell).injective
  rw [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.apply_symm_apply, mapEquiv_rankOne]

def coordinateTau (k : ℕ) : (Fin (1 + 2 * k) → F2) →ₗ[F2] F2 :=
  ActualHomogeneous.tau.comp (domainCoordinates k).symm.toLinearMap

theorem functionalEquiv_tau (k : ℕ) :
    functionalEquiv k ActualHomogeneous.tau =
      Inverse.Shortcode.functionalRow (coordinateTau k) := by
  ext j
  rw [functionalEquiv_apply]
  rfl

theorem mapEquiv_symm_firstBit_shift (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (a : Fin ell → F2) :
    (mapEquiv k ell).symm
        (M + Inverse.Shortcode.rankOne a (Inverse.Shortcode.functionalRow (coordinateTau k))) =
      (mapEquiv k ell).symm M + ActualHomogeneous.tau.smulRight a := by
  rw [← functionalEquiv_tau]
  exact mapEquiv_symm_add_rankOne k ell M ActualHomogeneous.tau a

theorem affine_evaluation (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (z : Fin (1 + 2 * k) → F2)
    (u : Fin ell → F2) :
    Inverse.Shortcode.evaluate M z + u =
      (mapEquiv k ell).symm M ((domainCoordinates k).symm z) + u := by
  change Inverse.Shortcode.evaluate M z + u =
    Matrix.toLin' M ((domainCoordinates k) ((domainCoordinates k).symm z)) + u
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem mapEquiv_rowAdvice (k ell r : ℕ)
    (A : (Fin ell → F2) →ₗ[F2] (Fin r → F2))
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k r (A.comp M) =
      Inverse.RowErasureMatrix.rowAdvice (LinearMap.toMatrix' A) (mapEquiv k ell M) := by
  change LinearMap.toMatrix' (A.comp (M.comp (domainCoordinates k).symm.toLinearMap)) = _
  rw [LinearMap.toMatrix'_comp]
  rfl

private theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

/-- Coordinate change preserves the complete uniform matrix equality test. -/
theorem shortcodeAcceptance_eq (k ell : ℕ)
    (f : (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) → (Fin ell → F2)) :
    SurrogateFibers.shortcodeAcceptance f =
      Inverse.Shortcode.equalityAcceptance (fun M => f ((mapEquiv k ell).symm M)) := by
  unfold SurrogateFibers.shortcodeAcceptance Inverse.Shortcode.equalityAcceptance
  apply Fintype.expect_equiv (mapEquiv k ell).toEquiv
  intro M
  apply Finset.expect_congr rfl
  intro a _
  apply Fintype.expect_equiv (functionalEquiv k).toEquiv
  intro l
  simp only [LinearEquiv.coe_toEquiv, mapEquiv_symm_add_rankOne,
    LinearEquiv.symm_apply_apply]
  exact indicator_congr _ _ _ _ Iff.rfl

end
end UniqueGamesTheorem.Decoder.MatrixCoordinates

end

end OAI

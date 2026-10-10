import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix
open scoped Matrix.Norms.Elementwise

def gradientColumns {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) : Matrix (Fin 3) m ℝ :=
  (LinearMap.toMatrix' D.toLinearMap)ᵀ

lemma gradientColumns_apply {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (v : Fin 3 → ℝ) :
    (gradientColumns D)ᵀ *ᵥ v = D v := by
  simp only [gradientColumns, transpose_transpose, LinearMap.toMatrix'_mulVec,
    ContinuousLinearMap.coe_coe]

lemma gradientColumns_rank {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (hD : Function.Surjective D) :
    LinearIndependent ℝ (gradientColumns D).col := by
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let M := LinearMap.toMatrix' D.toLinearMap
  let N := LinearMap.toMatrix' Q.toLinearMap
  have hMN : M * N = 1 := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, M, N, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    apply LinearMap.ext
    intro v
    exact hQ v
  have hNM : Nᵀ * gradientColumns D = 1 := by
    rw [gradientColumns, ← Matrix.transpose_mul, hMN, transpose_one]
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  have h := congrArg Nᵀ.mulVec hvw
  simpa only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using h

lemma gradientColumns_pairing {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (F : Matrix (Fin 3) m ℝ) (i j : m) :
    D (F.col j) i = ((gradientColumns D)ᵀ * F) i j := by
  rw [← gradientColumns_apply]
  rfl

theorem symmetric_wave_polarization
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.IsSymm)
    (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (hL : ∀ v, L (B *ᵥ v) = 0) :
    let R := (B * gradientColumns D).col
    D (R 0) 1 = D (R 1) 0 ∧ ∀ j, L (R j) = 0 := by
  dsimp only
  constructor
  · rw [gradientColumns_pairing, gradientColumns_pairing]
    have hsym : ((gradientColumns D)ᵀ * (B * gradientColumns D)).IsSymm := by
      unfold Matrix.IsSymm
      rw [transpose_mul, transpose_mul, transpose_transpose, hB]
      exact Matrix.mul_assoc _ _ _
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hsym
  · intro j
    convert hL ((gradientColumns D).col j) using 1
    rfl

lemma diagonal_difference_normal_annihilates (i : Fin 3) (α β : Fin 3 → ℝ)
    (h : α i = β i) (v : Fin 3 → ℝ) :
    ((Matrix.diagonal α - Matrix.diagonal β) *ᵥ v) i = 0 := by
  simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal, h, sub_self]

end ScalarConductivity

end

end OAI

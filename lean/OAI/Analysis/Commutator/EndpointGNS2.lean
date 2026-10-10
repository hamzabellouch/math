import Mathlib
import OAI.Analysis.Commutator.EndpointGNS
import OAI.Analysis.Commutator.EndpointModule2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def stageRepresentation (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) :
    Matrix I I ℂ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) := τ.gnsStarAlgHom.comp φ

omit [Nonempty I] in
@[simp] lemma stageRepresentation_vacuum (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : Matrix I I ℂ) :
    stageRepresentation τ φ a (vacuum τ) = stageVector τ φ a := by
  change τ.gnsStarAlgHom (φ a) (τ.toPreGNS 1 : τ.GNS) = (τ.toPreGNS (φ a) : τ.GNS)
  rw [left_coe, mul_one]

include hτ h1 in
lemma stageRepresentation_trace (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : Matrix I I ℂ) :
    inner ℂ (vacuum τ) (stageRepresentation τ φ a (vacuum τ)) = normalizedTrace a := by
  rw [stageRepresentation_vacuum]
  change inner ℂ (vacuum τ) (algebraVector τ (φ a)) = _
  rw [inner_vacuum_algebraVector, stage_trace τ hτ h1 φ]
  rfl

include hτ h1 in
lemma norm_centeredStageVector_single (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (i j : I) :
    ‖centeredStageVector τ φ (Matrix.single i j 1)‖ ≤ Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  calc
    _ ≤ ‖stageVector τ φ (Matrix.single i j 1)‖ :=
      norm_center_le (vacuum τ) _
    _ = _ := by
      rw [← stageRepresentation_vacuum]
      exact MatrixModule.norm_vector_single (stageRepresentation τ φ) (vacuum τ)
        (stageRepresentation_trace τ hτ h1 φ) i j

noncomputable def wordLeft (a : A) (k : ℕ) :
    wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) k :=
  HilbertTensor.map (τ.gnsStarAlgHom a) (1 : power (zeroSpace τ) k →L[ℂ] power (zeroSpace τ) k)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include hτ h1 in
lemma stageCoefficient_rank_one (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (hY : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (b : Option (Fin k ⊕ Fin l) → I)
    (σ : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
    ‖stageCoefficient τ Y φ (fun j => Matrix.single (b (σ j)) (b j) 1)‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ (Fintype.card (Option (Fin k ⊕ Fin l)) - 1) := by
  let v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ :=
    fun j => Matrix.single (b (σ j)) (b j) 1
  have hleft (a : Matrix I I ℂ) :
      Y.comp (HilbertTensor.map (stageRepresentation τ φ a)
        (1 : power (zeroSpace τ) k →L[ℂ] power (zeroSpace τ) k)) =
      (HilbertTensor.map (stageRepresentation τ φ a)
        (1 : power (zeroSpace τ) l →L[ℂ] power (zeroSpace τ) l)).comp Y := hY (φ a)
  have h := MatrixModule.endpoint_unit_bound (stageRepresentation τ φ) (vacuum τ)
    (stageRepresentation_trace τ hτ h1 φ) Y hleft (b none) (b (σ none))
    (pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i)))))
    (pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i))))))
  have hs (j) : star (v j) = Matrix.single (b j) (b (σ j)) 1 := by
    simp only [v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
  have hcoeff : ‖stageCoefficient τ Y φ v‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        ‖pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i))))‖ *
        ‖pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i)))))‖ := by
    change ‖coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
      (stageVector τ φ) (centeredStageVector τ φ) v‖ ≤ _
    simpa only [coefficient, word, hs, stageRepresentation_vacuum] using h
  have hx : ‖pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i))))‖ ≤
      (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ k := by
    rw [norm_pure]
    calc
      _ ≤ ∏ _ : Fin k, Real.sqrt (Fintype.card I : ℝ)⁻¹ :=
        Finset.prod_le_prod₀ (by intros; positivity) (fun i _ => norm_centeredStageVector_single τ hτ h1 φ _ _)
      _ = _ := by simp
  have hz : ‖pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i)))))‖ ≤
      (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ l := by
    rw [norm_pure]
    calc
      _ ≤ ∏ _ : Fin l, Real.sqrt (Fintype.card I : ℝ)⁻¹ :=
        Finset.prod_le_prod₀ (by intros; positivity) (fun i _ => by
          rw [hs]; exact norm_centeredStageVector_single τ hτ h1 φ _ _)
      _ = _ := by simp
  calc
    _ ≤ _ := hcoeff
    _ ≤ ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ k * (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ l := by
      gcongr
    _ = _ := by simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Nat.add_sub_cancel_right, pow_add]; ring

end Kadison.TracialGNS
end

end OAI

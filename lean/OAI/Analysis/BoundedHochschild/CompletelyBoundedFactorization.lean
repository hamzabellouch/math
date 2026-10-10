import OAI.Analysis.BoundedHochschild.PaulsenEntries
import OAI.Analysis.BoundedHochschild.StinespringEmbedding

namespace OAI

/-! Factor a completely contractive map through an actual star representation. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure OperatorFactorization (T : A →ₗ[ℂ] (H →L[ℂ] H)) (C : ℝ) where
  K : Type (max u v)
  [normed : NormedAddCommGroup K]
  [innerSpace : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  representation : A →⋆ₐ[ℂ] (K →L[ℂ] K)
  leftMap : H →L[ℂ] K
  rightMap : H →L[ℂ] K
  bound : ‖leftMap‖ * ‖rightMap‖ ≤ C
  factorization : ∀ a, T a = leftMap.adjoint.comp ((representation a).comp rightMap)

attribute [instance] OperatorFactorization.normed OperatorFactorization.innerSpace
  OperatorFactorization.complete

variable [Nontrivial A] [Nontrivial H]

theorem factorization_of_complete_contraction (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖) :
    Nonempty (OperatorFactorization T 1) := by
  obtain ⟨f, hf, _⟩ := NaimarkZFC.exists_norming_state (1 : A)
  have hf1 : f 1 = 1 := ((NaimarkZFC.isState_iff f).mp hf).1
  obtain ⟨Φ, hΦ1, hΦ⟩ := exists_paulsen_extension f.toLinearMap hf1 T hT
  let V := stinespringEmbedding Φ
  let π := (stinespringRepresentation Φ).comp (matrixScalarHom 2)
  let J₀ := (doubleCoordinate (H := H) 0).toContinuousLinearMap
  let J₁ := (doubleCoordinate (H := H) 1).toContinuousLinearMap
  let E := singleCStarMatrix (0 : Fin 2) 1 (1 : A)
  let L := V.comp J₀
  let R := (stinespringRepresentation Φ E).comp (V.comp J₁)
  have hV : ‖V‖ ≤ 1 := by
    simpa only [V, hΦ1, CStarRing.norm_one, Real.sqrt_one] using stinespringEmbedding_norm_le Φ
  have hJ (i : Fin 2) : ‖(doubleCoordinate (H := H) i).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ξ
    simp
  have hL : ‖L‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le V J₀).trans
      (by simpa only [one_mul] using mul_le_mul hV (hJ 0) (norm_nonneg J₀) zero_le_one)
  have hR : ‖R‖ ≤ 1 := by
    have hE : ‖stinespringRepresentation Φ E‖ ≤ 1 :=
      (NonUnitalStarAlgHom.norm_apply_le _ _).trans single_offDiagonal_norm_le_one
    have hVJ : ‖V.comp J₁‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul hV (hJ 1) (norm_nonneg J₁) zero_le_one)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul hE hVJ (norm_nonneg (V.comp J₁)) zero_le_one)
  refine ⟨{
    K := StinespringSpace Φ
    representation := π
    leftMap := L
    rightMap := R
    bound := ?_
    factorization := ?_ }⟩
  · simpa only [one_mul] using mul_le_mul hL hR (norm_nonneg R) zero_le_one
  · intro a
    rw [← paulsenExtension_entry f.toLinearMap T Φ hΦ a, stinespring_factorization,
      single_offDiagonal_factor a, map_mul]
    dsimp only [L, R, π, V, E, StarAlgHom.comp_apply]
    rw [ContinuousLinearMap.adjoint_comp]
    rfl

theorem factorization_of_complete_bound (T : A →ₗ[ℂ] (H →L[ℂ] H))
    {C : ℝ} (hC : 0 < C)
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ C * ‖X‖) :
    Nonempty (OperatorFactorization T C) := by
  let U : A →ₗ[ℂ] (H →L[ℂ] H) := (C : ℂ)⁻¹ • T
  have hU : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map U‖ ≤ ‖X‖ := by
    intro n X
    have he : X.map U = (C : ℂ)⁻¹ • X.map T := by
      apply CStarMatrix.ext
      intro i j
      rfl
    rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    calc
      C⁻¹ * ‖X.map T‖ ≤ C⁻¹ * (C * ‖X‖) :=
        mul_le_mul_of_nonneg_left (hT n X) (inv_nonneg.mpr hC.le)
      _ = ‖X‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  obtain ⟨F⟩ := factorization_of_complete_contraction U hU
  refine ⟨{
    K := F.K
    representation := F.representation
    leftMap := F.leftMap
    rightMap := (C : ℂ) • F.rightMap
    bound := ?_
    factorization := ?_ }⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    calc
      ‖F.leftMap‖ * (C * ‖F.rightMap‖) = C * (‖F.leftMap‖ * ‖F.rightMap‖) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left F.bound hC.le
      _ = C := mul_one C
  · intro a
    calc
      T a = (C : ℂ) • U a := by simp [U, hC.ne']
      _ = F.leftMap.adjoint.comp
          ((F.representation a).comp ((C : ℂ) • F.rightMap)) := by
        rw [F.factorization]
        simp only [ContinuousLinearMap.comp_smul]

end BoundedHochschild.KadisonRingrose

end

end OAI

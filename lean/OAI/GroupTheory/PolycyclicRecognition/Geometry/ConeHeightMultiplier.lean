import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeQuotientHaar

namespace OAI

/-! # The quotient Haar character in canonical height coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold BigOperators

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The positive trace coefficients give the exact Haar multiplier as a
linear functional on the already chosen canonical height space. -/
theorem exists_cone_haar_height_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij
          (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (ell (eW (heightProjection T.character (h : L))))) * μ S := by
  obtain ⟨μ, c, hμ, hout, hin, _, hvol⟩ :=
    M.exists_cone_haar_multiplier T C hadd Q ExpQ hExpQ hbij haar
  let ell := (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap
  refine ⟨μ, ell, c, hμ, hout, hin, rfl, ?_⟩
  intro h S
  have heval : ell (eW (heightProjection T.character (h : L))) =
      ∑ i, (c i : ℝ) * M.weight i h := by
    simp only [ell, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, cartanHeightWeight_projection]
  rw [heval]
  exact hvol h S

end CartanWordModel

/-- A uniform height error controls the Haar multiplier at every anchor.
The location of the translated quotient set never enters the estimate. -/
theorem haar_image_le_of_height_error
    {W Q : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace Q]
    (ell : W →L[ℝ] ℝ) (μ : Measure Q) (α : Q ≃ Q) (S : Set Q)
    (height offset : W) (r ε : ℝ)
    (hvol : μ (α '' S) = ENNReal.ofReal (Real.exp (ell height)) * μ S)
    (herror : ‖height + r • offset‖ ≤ ε) :
    μ (α '' S) ≤ ENNReal.ofReal
      (Real.exp (-ell offset * r + ‖ell‖ * ε)) * μ S := by
  have hle : ell height + r * ell offset ≤ ‖ell‖ * ε := by
    have hh := (le_abs_self (ell (height + r • offset))).trans
      ((ell.le_opNorm (height + r • offset)).trans
        (mul_le_mul_of_nonneg_left herror (norm_nonneg ell)))
    simpa only [map_add, map_smul, smul_eq_mul] using hh
  rw [hvol]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (by linarith))) le_rfl

end PolycyclicRecognition

end

end OAI

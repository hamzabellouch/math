import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHaarImage

namespace OAI

/-! # The exact positive character of quotient Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- A single Haar measure has the quotient Jacobian character for every
Cartan parameter. The character coefficients are positive exactly on the
retained generators. -/
theorem exists_cone_haar_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (c : Fin M.letterCount → ℕ), μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      (∀ h : H, Measure.map
        (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h)) μ =
        ENNReal.ofReal (Real.exp (-(∑ i, (c i : ℝ) * M.weight i h))) • μ) ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (∑ i, (c i : ℝ) * M.weight i h)) * μ S := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ :=
    haar.2 ExpQ hExpQ (Q.tangent_nilpotent (M.coneQuotient_nilpotent C))
  let b := Module.finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  let μ := Measure.map ((ExpQ ∘ Q.equiv) ∘ b.equivFun.symm) volume
  obtain ⟨c, hout, hin, htrace⟩ := M.exists_positive_cone_trace_coefficients C hadd
  refine ⟨μ, c, ?_, hout, hin, ?_, ?_⟩
  · have hf : (ExpQ ∘ Q.equiv) ∘ b.equivFun.symm =
        ExpQ ∘ (b.map Q.equiv.toLinearEquiv).equivFun.symm := by
      funext x
      rw [Basis.map_equivFun]
      rfl
    dsimp only [μ]
    rw [hf]
    exact hhaar _ (b.map Q.equiv.toLinearEquiv)
  · intro h
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    have hm := exponentialConjugate_map_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h)
    rw [hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
    exact hm
  · intro h S
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    exact exponentialConjugate_image_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h) _ hd S

end PolycyclicRecognition.CartanWordModel

end

end OAI

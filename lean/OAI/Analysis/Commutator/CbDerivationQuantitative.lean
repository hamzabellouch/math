import Mathlib
import OAI.Analysis.Commutator.CbDerivation
import OAI.Analysis.Commutator.CyclicCbUnconditional

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.CbFactor

open RectangularColumn CyclicColumns

variable {A K F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance : NormedAddCommGroup (K →L[ℂ] F) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (K →L[ℂ] F) := ContinuousLinearMap.toNormedSpace

omit [CompleteSpace K] [CompleteSpace F] in
lemma matrixAction_smul {ι : Type*} [Fintype ι] (c : ℝ) (D : ι → ι → K →L[ℂ] F) :
    matrixAction (fun i j => c • D i j)=c • matrixAction D := by
  ext x i
  simp [Finset.smul_sum]

theorem rectangular_implementation_quantitative (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b))
    {c : ℝ} (hc : 0≤c)
    (hcb : ∀ (ι : Type) [Fintype ι] (X : CStarMatrix ι ι A),
      ‖matrixAction (fun i j => D (X i j))‖≤c*‖D‖*‖X‖) :
    ∃ V : K →L[ℂ] F,‖V‖≤((1+c)^2)*‖D‖ ∧ ∀ a : A,D a=V.comp (σ a)-(lam a).comp V := by
  by_cases hz : D=0
  · refine ⟨0,by simp [hz],?_⟩
    intro a
    simp [hz]
  have hd : 0<‖D‖ := norm_pos_iff.mpr hz
  let Δ : A →L[ℂ] (K →L[ℂ] F) := ‖D‖⁻¹ • D
  have hΔ : ∀ a b,Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b) := by
    intro a b
    simp only [Δ,smul_apply,hD,smul_add,
      ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul]
  have hnorm : ∀ (ι : Type) [Fintype ι] (X : CStarMatrix ι ι A),
      ‖matrixAction (fun i j => Δ (X i j))‖≤c*‖X‖ := by
    intro ι _ X
    change ‖matrixAction (fun i j => ‖D‖⁻¹ • D (X i j))‖≤c*‖X‖
    rw [matrixAction_smul]
    calc
      _ ≤ ‖‖D‖⁻¹‖*‖matrixAction (fun i j => D (X i j))‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖D‖⁻¹*(c*‖D‖*‖X‖) := by
        rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
        exact mul_le_mul_of_nonneg_left (hcb ι X) (inv_nonneg.mpr hd.le)
      _ = c*‖X‖ := by field_simp
  obtain ⟨V,hV,himpl⟩ := rectangular_implementation σ lam Δ hΔ hc hnorm
  refine ⟨‖D‖ • V,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
      ((mul_le_mul_of_nonneg_left hV (norm_nonneg (‖D‖))).trans_eq (by
        rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg D)]; ring))
  · intro a
    have hh : ‖D‖ • Δ a=D a := by
      simp only [Δ,smul_apply,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    rw [←hh,himpl,smul_sub,ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul]

theorem cyclic_implementation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b))
    (Ω : K) (hΩ : DenseRange (fun a : A => σ a Ω)) :
    ∃ V : K →L[ℂ] F,‖V‖≤289*‖D‖ ∧ ∀ a : A,D a=V.comp (σ a)-(lam a).comp V := by
  have h := rectangular_implementation_quantitative σ lam D hD (c:=16) (by norm_num)
    (fun _ _ X => cyclic_matrix_bound_unconditional σ lam D hD Ω hΩ X)
  norm_num at h
  exact h

end Kadison.CbFactor

end

end
end

end OAI

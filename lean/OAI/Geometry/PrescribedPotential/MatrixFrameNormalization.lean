import Mathlib
import OAI.Geometry.PrescribedPotential.LinearFrameCalculus
import OAI.Geometry.PrescribedPotential.TracePositivity

namespace OAI

/-! Matrix Frame Normalization. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def matrixFrame (B : Matrix (Fin n) (Fin n) ℂ) : V n →L[ℂ] V n :=
  (Matrix.toLin' B).toContinuousLinearMap

lemma frameMatrix_matrixFrame (B : Matrix (Fin n) (Fin n) ℂ) :
    frameMatrix (matrixFrame B) = B := by
  change LinearMap.toMatrix' (Matrix.toLin' B) = B
  exact LinearMap.toMatrix'_toLin' B

lemma matrixFrame_apply (B : Matrix (Fin n) (Fin n) ℂ) (v : V n) :
    matrixFrame B v = B*ᵥv := rfl

lemma normalized_frame (M : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) (hp : (M z).PosDef) :
    ∃ (B : V n →L[ℂ] V n) (w : V n), IsUnit (frameMatrix B) ∧ B w = z ∧ pullMetric B M w = 1 := by
  obtain ⟨C,hC,hEq⟩ := whitening (M z) hp
  obtain ⟨w,hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hC) z
  refine ⟨matrixFrame C,w,?_,?_,?_⟩
  · rwa [frameMatrix_matrixFrame]
  · exact hw
  · unfold pullMetric
    rw [frameMatrix_matrixFrame,matrixFrame_apply,hw]
    exact hEq

lemma pullMetric_positive {U : Set (V n)} (B : V n →L[ℂ] V n)
    (hB : IsUnit (frameMatrix B)) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hp : ∀ y ∈ U, (M y).PosDef) : ∀ y ∈ B ⁻¹' U, (pullMetric B M y).PosDef := by
  intro y hy
  exact (hp (B y) hy).conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hB)

lemma matrix_inverse_trace_congruence (B M G : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B) :
    ((Bᴴ*M*B)⁻¹*(Bᴴ*G*B)).trace = (M⁻¹*G).trace := by
  have hc : B*B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hd : Bᴴ⁻¹*Bᴴ = 1 := by
    rw [← Matrix.conjTranspose_nonsing_inv,← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  simp only [Matrix.mul_inv_rev,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ,hd,Matrix.one_mul]
  rw [← Matrix.mul_assoc M⁻¹,← Matrix.mul_assoc B⁻¹,Matrix.trace_mul_cycle,hc,Matrix.one_mul]
end KaehlerCalculus

end
end

end OAI

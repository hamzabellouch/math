import OAI.Geometry.NodalSets.Charts.FiniteChartDerivativeSeminorm
import OAI.Geometry.NodalSets.Charts.SupportedFiniteAtlasBounds
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientSmooth

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsic_coefficient_chart_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (p : Base) :
    ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p) :=
  contDiff_iff_contDiffAt.mpr (fun z ↦ intrinsicChartCoefficient_smoothAt A hA hs hp rho hr p
    (by rw [centeredSphereChart_target]; trivial))

lemma sphereCoefficientDistance_self (P : Finset Base) (J : ℕ) (A : IntrinsicTensor) (rho : Base → ℝ) :
    sphereCoefficientDistance P J A rho A rho = 0 := by
  simp only [sphereCoefficientDistance,sub_self]
  exact finiteChartDerivativeSize_zero P sphereAtlasCore_compact J

lemma sphereCoefficientDistance_nonneg (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p)) :
    0 ≤ sphereCoefficientDistance P J A rho B sigma :=
  finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _ (fun p hp ↦ (hB p hp).sub (hA p hp))

lemma sphereCoefficientDistance_symm (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p)) :
    sphereCoefficientDistance P J B sigma A rho = sphereCoefficientDistance P J A rho B sigma := by
  have h := finiteChartDerivativeSize_smul P sphereAtlasCore_compact J (-1:ℝ)
    (fun p z ↦ intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)
    (fun p hp ↦ (hB p hp).sub (hA p hp))
  simpa only [neg_one_smul,neg_sub,norm_neg,norm_one,one_mul,sphereCoefficientDistance] using h

lemma sphereCoefficientDistance_triangle (P : Finset Base) (J : ℕ)
    (A B C : IntrinsicTensor) (rho sigma tau : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p))
    (hC : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient C tau p)) :
    sphereCoefficientDistance P J A rho C tau ≤
      sphereCoefficientDistance P J A rho B sigma+sphereCoefficientDistance P J B sigma C tau := by
  have he : (fun p z ↦ intrinsicChartCoefficient C tau p z-intrinsicChartCoefficient A rho p z) =
      (fun p z ↦ (intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)+
        (intrinsicChartCoefficient C tau p z-intrinsicChartCoefficient B sigma p z)) := by
    funext p z
    abel
  unfold sphereCoefficientDistance
  rw [he]
  exact finiteChartDerivativeSize_add_le P sphereAtlasCore_compact J _ _
    (fun p hp ↦ (hB p hp).sub (hA p hp)) (fun p hp ↦ (hC p hp).sub (hB p hp))

end
end Yau.Target

end OAI

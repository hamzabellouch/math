import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiCutoffCalculus

namespace OAI

/-! Calabi Cutoff Differential. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

def cutoffCoefficient (d : ℕ) (M B C K δ : ℝ) : ℝ :=
  (B^2*C+(d:ℝ)^2*M*B+(4*(d:ℝ)^2*M*B)^2*K/2+1)/δ

lemma cutoffCoefficient_pos {M B C K δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hδ : 0 < δ) :
    0 < cutoffCoefficient d M B C K δ := by unfold cutoffCoefficient; positivity

lemma cutoff_test_lower_bound (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.PosDef)
    {χ S T : Coordinates d → ℝ} {z : Coordinates d}
    (hχ : ContDiffAt ℝ ∞ χ z) (hS : ContDiffAt ℝ ∞ S z) (hT : ContDiffAt ℝ ∞ T z)
    {M B C K δ R E : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hδ : 0 < δ) (hE : 0 ≤ E) (hSz : 0 ≤ S z)
    (hI : ‖H⁻¹‖ ≤ M) (hχB : |χ z| ≤ B) (hDχ : ‖holRealDeriv χ z‖ ≤ B)
    (hDDχ : ‖PotentialKaehler.potentialMatrix (fun y => χ y*χ y) z‖ ≤ B)
    (hDS : ‖holRealDeriv S z‖^2 ≤ K*S z*E)
    (hLS : E-C*(S z+1) ≤ localLap H S z)
    (hLT : δ*S z-R ≤ localLap H T z) :
    S z-B^2*C-cutoffCoefficient d M B C K δ*R ≤
      localLap H (fun y => χ y*χ y*S y+cutoffCoefficient d M B C K δ*T y) z := by
  let a := cutoffCoefficient d M B C K δ
  have ha : 0 ≤ a := (cutoffCoefficient_pos hM hB hC hK hδ).le
  have had : a*δ = B^2*C+(d:ℝ)^2*M*B+(4*(d:ℝ)^2*M*B)^2*K/2+1 := by
    dsimp [a,cutoffCoefficient]
    exact div_mul_cancel₀ _ hδ.ne'
  have hc2 : (χ z)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hχB
  have hχlap : -(d:ℝ)^2*M*B ≤ localLap H (fun y => χ y*χ y) z := by
    have hh := (localLap_abs_bound H (fun y => χ y*χ y) z).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hI (sq_nonneg _)) hDDχ (norm_nonneg _) (by positivity))
    convert! (abs_le.mp hh).1 using 1
    ring
  have hcross := cutoff_cross_bound H (hχ.differentiableAt (by simp)) hM hB hK hSz hE hI hDχ hDS
  have h1 := mul_le_mul_of_nonneg_left hLS (sq_nonneg (χ z))
  have h2 := mul_le_mul_of_nonneg_left hχlap hSz
  have h3 := mul_le_mul_of_nonneg_left hLT ha
  have h4 := mul_le_mul_of_nonneg_right hc2 (show 0 ≤ C*(S z+1) by positivity)
  have h5 : 0 ≤ (χ z)^2*E := mul_nonneg (sq_nonneg _) hE
  rw [localLap_affine ((hχ.mul hχ).mul hS) hT,localLap,
    trace_hessian_product (hχ.mul hχ) hS H hH.isHermitian]
  change S z-B^2*C-a*R ≤ χ z*χ z*localLap H S z+
    S z*localLap H (fun y => χ y*χ y) z+
    2*(gradientPair H (holRealDeriv (fun y => χ y*χ y) z) (holRealDeriv S z)).re+a*localLap H T z
  nlinarith [congrArg (fun t : ℝ => t*S z) had]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.VolumePathRicci

namespace OAI

/-! Calabi Cutoff Calculus. -/

section

 
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ}

def localLap (H : Matrix (Fin d) (Fin d) ℂ) (f : Coordinates d → ℝ)
    (z : Coordinates d) : ℝ := (H⁻¹*PotentialKaehler.potentialMatrix f z).trace.re

lemma localLap_affine {f h : Coordinates d → ℝ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (hh : ContDiffAt ℝ ∞ h z)
    (H : Matrix (Fin d) (Fin d) ℂ) (a : ℝ) :
    localLap H (fun y => f y+a*h y) z = localLap H f z+a*localLap H h z := by
  have he := PotentialKaehler.potentialMatrix_affine hf hh a 0
  simp only [add_zero] at he
  unfold localLap
  rw [he,mul_add,Matrix.mul_smul,trace_add,trace_smul,Complex.add_re]
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma localLap_abs_bound (H : Matrix (Fin d) (Fin d) ℂ) (f : Coordinates d → ℝ)
    (z : Coordinates d) : |localLap H f z| ≤
      (d:ℝ)^2*‖H⁻¹‖*‖PotentialKaehler.potentialMatrix f z‖ := by
  apply (Complex.abs_re_le_norm _).trans
  exact (trace_entry_bound (fun i j => norm_entry_le_entrywise_sup_norm
    (H⁻¹*PotentialKaehler.potentialMatrix f z) (i:=i) (j:=j))).trans
    ((mul_le_mul_of_nonneg_left (matrix_norm_mul_le _ _) (by positivity)).trans_eq (by
      simp only [Fintype.card_fin]; ring))

lemma gradientPair_norm_bound (H : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d → ℂ) :
    ‖gradientPair H p q‖ ≤ (d:ℝ)^2*‖H⁻¹‖*‖p‖*‖q‖ := by
  unfold gradientPair
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin d, ∑ _i : Fin d, ‖H⁻¹‖*‖p‖*‖q‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (norm_entry_le_entrywise_sup_norm _)
        (norm_le_pi_norm p i) (norm_nonneg _) (norm_nonneg _))
        (norm_le_pi_norm q j) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma holRealDeriv_square {χ : Coordinates d → ℝ} {z : Coordinates d}
    (hχ : DifferentiableAt ℝ χ z) :
    holRealDeriv (fun y => χ y*χ y) z = (2*(χ z : ℂ)) • holRealDeriv χ z := by
  funext a
  rw [holRealDeriv_mul hχ hχ]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma norm_pi_sq_bound {ι : Type*} [Fintype ι] {v : ι → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖^2 ≤ B) : ‖v‖^2 ≤ B := by
  have hn : ‖v‖ ≤ Real.sqrt B := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
    (fun i => (Real.le_sqrt (norm_nonneg _) hB).mpr (hv i))
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn).trans_eq (Real.sq_sqrt hB)

lemma square_absorb {a x y : ℝ} (_ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hb : a^2 ≤ x*y) : a ≤ (x+y)/2 := by
  nlinarith [sq_nonneg (x-y)]

lemma cutoff_cross_bound (H : Matrix (Fin d) (Fin d) ℂ)
    {χ S : Coordinates d → ℝ} {z : Coordinates d}
    (hχ : DifferentiableAt ℝ χ z) {M B K s E : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hK : 0 ≤ K) (hs : 0 ≤ s) (hE : 0 ≤ E)
    (hI : ‖H⁻¹‖ ≤ M) (hDχ : ‖holRealDeriv χ z‖ ≤ B)
    (hDS : ‖holRealDeriv S z‖^2 ≤ K*s*E) :
    2*(gradientPair H (holRealDeriv (fun y => χ y*χ y) z) (holRealDeriv S z)).re ≥
      -(χ z)^2*E/2-((4*(d:ℝ)^2*M*B)^2*K)*s/2 := by
  let L := 4*(d:ℝ)^2*M*B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hn : 2*‖gradientPair H (holRealDeriv (fun y => χ y*χ y) z)
      (holRealDeriv S z)‖ ≤ L*|χ z| *‖holRealDeriv S z‖ := by
    apply (mul_le_mul_of_nonneg_left (gradientPair_norm_bound _ _ _) (by norm_num)).trans
    rw [holRealDeriv_square hχ,norm_smul,norm_mul]
    norm_num only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat]
    calc
      _ ≤ 2*((d:ℝ)^2*M*(2*|χ z| *B)*‖holRealDeriv S z‖) := by
        gcongr
      _ = _ := by dsimp [L]; ring
  have hsq : (L*|χ z| *‖holRealDeriv S z‖)^2 ≤ ((χ z)^2*E)*(L^2*K*s) := by
    have hh := mul_le_mul_of_nonneg_left hDS (show 0 ≤ L^2*(χ z)^2 by positivity)
    calc
      _ = L^2*(χ z)^2*‖holRealDeriv S z‖^2 := by rw [mul_pow,mul_pow,sq_abs]
      _ ≤ L^2*(χ z)^2*(K*s*E) := hh
      _ = _ := by ring
  have ha := square_absorb (show 0 ≤ L*|χ z| *‖holRealDeriv S z‖ by positivity)
    (show 0 ≤ (χ z)^2*E by positivity) (show 0 ≤ L^2*K*s by positivity) hsq
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (gradientPair H (holRealDeriv (fun y => χ y*χ y) z) (holRealDeriv S z)))).1
  change _ ≥ -(χ z)^2*E/2-(L^2*K)*s/2
  linarith

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

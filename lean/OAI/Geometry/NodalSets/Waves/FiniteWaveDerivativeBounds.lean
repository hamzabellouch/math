import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientTail
import OAI.Geometry.NodalSets.Waves.GaussianWaveJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_contDiff (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) : ContDiff ℝ ∞ (gaussianWaveField V a) := by
  classical
  exact Complex.reCLM.contDiff.comp (ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i)))

lemma gaussianWaveField_iterated_bound (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (k : ℕ) (x : Coord) {R B : ℝ}
    (hR : 0 ≤ R) (ha : a ∈ coefficientEvent R)
    (hB : ∀ i, ‖iteratedFDeriv ℝ k (V i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (gaussianWaveField V a) x‖ ≤ (Fintype.card ι:ℝ)*R*B := by
  classical
  let W : Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i))
  have hr := realPart_iterated_norm_le W x hW.contDiffAt k
  change ‖iteratedFDeriv ℝ k (gaussianWaveField V a) x‖ ≤ _ at hr
  refine hr.trans ?_
  dsimp only [W]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((contDiff_const.mul (hV i)).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  have hb (i : ι) : ‖iteratedFDeriv ℝ k (fun z ↦ gaussianCoefficient a i*V i z) x‖ ≤ R*B := by
    change ‖iteratedFDeriv ℝ k (gaussianCoefficient a i • V i) x‖ ≤ R*B
    rw [iteratedFDeriv_const_smul_apply ((hV i).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul]
    exact (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hB i) hR)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hb i)
  simpa [mul_assoc] using hh

end
end Yau.Geometry

end OAI

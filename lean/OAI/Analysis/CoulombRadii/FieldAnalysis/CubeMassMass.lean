import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FirstParticleDensityNonneg
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinCubeEquiv

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma cubeMass_le_mass {n : ℕ} (ψ : H1Vector n) (b : ℝ) : cubeMass ψ b ≤ mass ψ := by
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ ∫ x : (Fin n × Fin 3) → ℝ, ‖ψ.value s (WithLp.toLp 2 x)‖^2 :=
      integral_mono_measure (finiteCubeMeasure_le_volume b) (ae_of_all _ (fun x => sq_nonneg _))
        ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)).norm.integrable_sq
    _ = _ := (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
      PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma cubeKinetic_le_kinetic {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    cubeKinetic ψ b ≤ kinetic ψ := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∫ x : (Fin n × Fin 3) → ℝ, ‖ψ.gradient s i (WithLp.toLp 2 x)‖^2 :=
      integral_mono_measure (finiteCubeMeasure_le_volume b) (ae_of_all _ (fun x => sq_nonneg _))
        ((ψ.partial_L2 s i).comp_measurePreserving (PiLp.volume_preserving_toLp _)).norm.integrable_sq
    _ = _ := (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
      PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.gradient s i x‖^2)

lemma cubeState_weighted {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b)
    (a : Fin n → SpinMode) :
    (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2 =
      (2*b^2/Real.pi^2)*(cubeSpectralWeight b a*‖cubeFermionCoefficient ψ b a‖^2) := by
  rw [cubeState_coefficient, cubeSpectralWeight_eq_neumann, ← Finset.mul_sum]
  field_simp

lemma cubeState_weighted_summable {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    Summable (fun a : Fin n → SpinMode => (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2) := by
  simp_rw [cubeState_weighted ψ hb]
  exact (cubeFermionCoefficient_energy_summable hn ψ hb).mul_left _

lemma cubeState_weighted_le {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    (∑' a : Fin n → SpinMode, (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2) ≤
      (2*b^2/Real.pi^2)*kinetic ψ := by
  simp_rw [cubeState_weighted ψ hb, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left ((cubeFermionCoefficient_energy_le hn ψ hb).trans
    (cubeKinetic_le_kinetic ψ b)) (by positivity)

lemma cubeRumin_constant {b : ℝ} (hb : 0 < b) :
    (32*(128/b^3))^(2/3:ℝ) = 256/b^2 := by
  rw [show 32*(128/b^3)=(16/b)^3 by ring, ← Real.rpow_natCast_mul (by positivity : 0 ≤ 16/b)]
  norm_num
  ring

theorem cube_density_power_bound {n : ℕ} (ψ : H1Vector (n+1)) (hψ : Antisymmetric ψ)
    (hm : mass ψ ≤ 1) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => (firstParticleDensity (μ := spinCubeMeasure b) (cubeState ψ) x)^(5/3:ℝ))
      (spinCubeMeasure b) ∧
    (∫ x, (firstParticleDensity (μ := spinCubeMeasure b) (cubeState ψ) x)^(5/3:ℝ)
      ∂(spinCubeMeasure b)) ≤ (256/b^2)*((n+1:ℕ):ℝ) + (8192/(3*Real.pi^2))*kinetic ψ := by
  let : Fact ((2:ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (spinCubeMeasure b) := isSeparable_of_sigmaFinite _
  have H := continuum_rumin_bound (ψ.cubeState_memLp b) (cubeState_antisymmetric hψ b)
    (by rw [cubeState_mass]; exact (cubeMass_le_mass ψ b).trans hm)
    (spinCubeMode b) (spinCubeMode_memLp b) (fun i j => by by_cases h : i = j <;> simpa [h] using spinCubeMode_inner hb i j) (spinCubeMode_complete hb)
    coarseCubeModes (fun a : SpinMode => (latticeRadius a.2)^2) (fun a => sq_nonneg _)
    coarseCubeModes_cutoff (by positivity : 0 < 128/b^3) (spinCubeMode_diagonal hb)
    (cubeState_weighted_summable (by omega) ψ hb)
  refine ⟨H.1, ?_⟩
  rw [cubeRumin_constant hb] at H
  have ht := cubeState_weighted_le (by omega) ψ hb
  calc
    _ ≤ _ := H.2
    _ ≤ (256/b^2)*((n+1:ℕ):ℝ)+(16/3:ℝ)*(256/b^2)*((2*b^2/Real.pi^2)*kinetic ψ) := by
      gcongr
    _ = _ := by field_simp; ring

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end
end

end OAI

import OAI.Analysis.TriangularHilbert.InitialAlgebra

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def arrayCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) : ℝ :=
  ∑ v, ∑ i, ∑ j, h^2*‖A v i j‖^3

lemma sum_three_shift (f : Three → ℝ) : (∑ v, f (v+2)) = ∑ v, f v := by
  simp [Fin.sum_univ_three]
  ring

lemma totalPlaneEnergy_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : 0 ≤ totalPlaneEnergy A h u d σ := by
  apply Finset.sum_nonneg
  intro v _
  exact integral_nonneg (fun _ => energy_gram_nonneg _)

lemma totalPlaneEnergy_le_mass (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v)
    {M : ℝ} (hM : 0 ≤ M) (hm : ∀ p v, (∑ i, heatWeights h u p σ v i) ≤ M) :
    totalPlaneEnergy A h u d σ ≤ 2*Real.sqrt 2*M*arrayCubic A h := by
  have hg p v i : 0 ≤ heatWeights h u p σ v i := (weight_pos hh (hσ v) (u i) (p v)).le
  have hb p v : heatEnergy A h u p σ v ≤ Real.sqrt 2*M*(edgeCubic A h u p σ v+edgeCubic A h u p σ (v+2)) := by
    have he := energy_star_le_hsCube (heatArray A h u p σ) v
    have h1 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) v
    have h2 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) (v+2)
    change hsCube (heatArray A h u p σ v) ≤ M*edgeCubic A h u p σ v at h1
    change hsCube (heatArray A h u p σ (v+2)) ≤ M*edgeCubic A h u p σ (v+2) at h2
    exact he.trans (by nlinarith [Real.sqrt_nonneg (2:ℝ)])
  have hi v : planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*((∑ i, ∑ j, h^2*‖A v i j‖^3)+(∑ i, ∑ j, h^2*‖A (v+2) i j‖^3)) := by
    have ht := integral_mono ((heatPlane_integrable A hh u d hσ).energy 2 v)
      (((edgeCubic_integrable A h u d σ hσ v 2).add
        (edgeCubic_integrable A h u d σ hσ (v+2) 2)).const_mul (Real.sqrt 2*M))
      (fun z => hb (chart 2 d z) v)
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul,integral_add (edgeCubic_integrable A h u d σ hσ v 2)
      (edgeCubic_integrable A h u d σ hσ (v+2) 2)] at ht
    change planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*(planeIntegral (fun p => edgeCubic A h u p σ v) d+
        planeIntegral (fun p => edgeCubic A h u p σ (v+2)) d) at ht
    simpa only [planeIntegral_edgeCubic A h u d σ hσ] using ht
  have ht := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) => hi v)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,
    sum_three_shift (fun v => ∑ i, ∑ j, h^2*‖A v i j‖^3)] at ht
  exact ht.trans_eq (by unfold arrayCubic; ring)

end
end TriangularHilbert.Heat
end

end OAI

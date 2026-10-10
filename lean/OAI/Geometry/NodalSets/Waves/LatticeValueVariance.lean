import OAI.Geometry.NodalSets.Waves.GaussianWaveJet
import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
noncomputable section

lemma gaussianWaveField_value_variance {ι : Type*} [Fintype ι]
    (V : ι → Coord → ℂ) (seed : Coord → ℝ) (x : Coord) :
    Var[fun coeff ↦ seed x+gaussianWaveField V coeff x; gaussianPairs] =
      ∑ i, ‖V i x‖^2 := by
  have he : (fun coeff ↦ gaussianWaveField V coeff x) = pairLinearSum (fun i ↦ V i x) := by
    funext coeff
    rw [pairLinearSum_eq_complex]
    simp only [gaussianWaveField,Complex.re_sum]
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : ι × Fin 2 ↦ gaussianReal 0 1))
    infer_instance
  have hc : Continuous (pairLinearSum (fun i ↦ V i x)) := by
    unfold pairLinearSum
    fun_prop
  change Var[(fun coeff ↦ seed x+(fun coeff ↦ gaussianWaveField V coeff x) coeff); gaussianPairs] = _
  rw [he,variance_const_add hc.aestronglyMeasurable,variance_pairLinearSum]

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma lattice_value_variance (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (seed : Coord → ℝ) (x : Coord) :
    Var[fun coeff ↦ seed x+gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff x;
      gaussianPairs] = (a.latticeSigma hUD n x)^2 := by
  rw [a.latticeSigma_sq]
  exact gaussianWaveField_value_variance _ seed x

end LocalCompactWaveData

end
end Yau.Geometry

end OAI

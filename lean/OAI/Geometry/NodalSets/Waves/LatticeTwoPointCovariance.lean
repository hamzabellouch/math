import OAI.Geometry.NodalSets.Charts.MetricFrequencyBounds
import OAI.Geometry.NodalSets.Waves.LatticeFullPlaneWaveApprox
import OAI.Geometry.NodalSets.Waves.PlaneWaveCovariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma lattice_plane_wave_variance (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x v : Coord) (s : ℝ) :
    Var[fun coeff ↦ gaussianWaveField (a.latticePlaneWaveCoefficient hUD n x s) coeff v;gaussianPairs] =
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
        sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
        ‖a.latticeAlpha hUD n x i‖^2 := by
  classical
  rw [gaussianWaveField_eq_pair,variance_pairLinearSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [latticePlaneWaveCoefficient]
  split_ifs <;> simp [planeWave_norm]

lemma lattice_plane_wave_covariance (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : Coord) (s tau : ℝ) (j : Fin 4) :
    cov[(fun coeff ↦ gaussianWaveField (a.latticePlaneWaveCoefficient hUD n x s) coeff 0),
      (fun coeff ↦ gaussianWaveField (a.latticePlaneWaveCoefficient hUD n x s)
        coeff (tau • Pi.single j 1));gaussianPairs] =
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
        sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
        ‖a.latticeAlpha hUD n x i‖^2 * Real.cos (tau *
          sourceFrequency (g (scaledLatticePoint n i.1))
            (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) s j) := by
  classical
  rw [gaussianWaveField_eq_pair,gaussianWaveField_eq_pair,covariance_pairLinearSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [latticePlaneWaveCoefficient]
  split_ifs
  · simp only [planeWave_zero,mul_one]
    rw [show planeWave (g (scaledLatticePoint n i.1)
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s (tau • Pi.single j 1) =
        Complex.exp (Complex.I * (tau * sourceFrequency (g (scaledLatticePoint n i.1))
          (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) s j : ℝ)) by
        simp [planeWave,sourceFrequency,map_smul,smul_eq_mul,mul_div_assoc]]
    exact complex_rotated_pairing _ _
  · simp

end LocalCompactWaveData
end
end Yau.Geometry

end OAI

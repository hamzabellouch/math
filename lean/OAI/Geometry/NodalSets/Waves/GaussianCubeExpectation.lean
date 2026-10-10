import OAI.Geometry.NodalSets.Elliptic.CubeControlExpectation
import OAI.Geometry.NodalSets.Elliptic.CubeGradientBound
import OAI.Geometry.NodalSets.Elliptic.FirstMomentFromSquare
import OAI.Geometry.NodalSets.Waves.GaussianGradientSupremum
import OAI.Geometry.NodalSets.Waves.GaussianPartialMeasurability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussian_partial_control_expectation (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) {C : ℝ}
    (hb : ∀ x : Coord, sourceEuclideanNorm x ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → Coord, ‖dirs‖ ≤ 1 →
        (∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x dirs)^2
          ∂gaussianPairs) ≤ C) (j : Fin 4) :
    (∫⁻ a, partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j]
      ∂gaussianPairs) ≤ 81 * ENNReal.ofReal (C+1) := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  have hF (a : ι × Fin 2 → ℝ) := hs.add (gaussianWaveField_contDiff V a hV)
  have hm (ds : List (Fin 4)) := (seeded_partial_joint_continuous V seed hV hs ds).measurable
  have hbound (ds : List (Fin 4)) (hd : ds.length ≤ 5) (x : Coord) (hx : InUnitCube x) :
      (∫⁻ a, ‖partialJet (fun z ↦ seed z+gaussianWaveField V a z) ds x‖ₑ ∂gaussianPairs) ≤
        ENNReal.ofReal (C+1) := by
    simp_rw [partialJet_eq_iterated _ (hF _)]
    exact lintegral_enorm_le_of_square
      (seeded_gaussian_derivative_memLp V seed hV hs _ _ _)
      (hb x (source_two_ball_of_inUnitCube hx) _ hd _ (partialDirs_norm_le_one ds))
  have hh := cubeControl_lintegral_le (fun a ↦ partialJet (fun z ↦ seed z+gaussianWaveField V a z))
      hm gaussianPairs 5 (ENNReal.ofReal (C+1)) hbound [0,1,2,3] [j] (by norm_num)
      0 (by intro i; norm_num)
  norm_num only [List.length_cons,List.length_nil] at hh
  exact hh

lemma gaussian_gradient_sup_le_control (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (K : Set Coord) [CompactSpace K] (hK : ∀ x ∈ K, sourceEuclideanNorm x ≤ 1)
    (a : ι × Fin 2 → ℝ) :
    ENNReal.ofReal (gaussianGradientSup V seed hV hs K a) ≤
      2 * ∑ j : Fin 4, partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j] := by
  rw [gaussianGradientSup,ofReal_norm,ContinuousMap.enorm_eq_iSup_enorm]
  apply iSup_le
  intro x
  have he : ‖gaussianGradientSection V seed hV hs K a x‖ =
      sourceEuclideanNorm (fun j ↦ fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z)
        x (Pi.single j 1)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [gaussianGradientSection_apply,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]
  rw [← ofReal_norm,he]
  exact gradient_enorm_le_cube_control _ (hs.add (gaussianWaveField_contDiff V a hV))
    x (hK x x.property)

lemma gaussian_control_measurable (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) (ds : List (Fin 4)) :
    Measurable (fun a ↦ partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) ds) := by
  unfold partialCubeControl
  exact cubeControl_measurable_at
    (fun a ↦ partialJet (fun z ↦ seed z+gaussianWaveField V a z))
    (fun ds ↦ (seeded_partial_joint_continuous V seed hV hs ds).measurable)
    [0,1,2,3] ds 0

 theorem gaussian_gradient_expectation_of_moments (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : Coord, sourceEuclideanNorm x ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → Coord, ‖dirs‖ ≤ 1 →
        (∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x dirs)^2
          ∂gaussianPairs) ≤ C)
    (K : Set Coord) [CompactSpace K] (hK : ∀ x ∈ K, sourceEuclideanNorm x ≤ 1) :
    (∫ a, gaussianGradientSup V seed hV hs K a ∂gaussianPairs) ≤ 648*(C+1) := by
  have hm (j : Fin 4) : Measurable (fun a ↦
      partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j]) :=
    gaussian_control_measurable V seed hV hs [j]
  have hh : (∫⁻ a, ENNReal.ofReal (gaussianGradientSup V seed hV hs K a) ∂gaussianPairs) ≤
      ENNReal.ofReal (648*(C+1)) := by
    calc
      _ ≤ ∫⁻ a, 2*∑ j : Fin 4, partialCubeControl
          (fun z ↦ seed z+gaussianWaveField V a z) [j] ∂gaussianPairs :=
        lintegral_mono (gaussian_gradient_sup_le_control V seed hV hs K hK)
      _ = 2 * ∑ j : Fin 4, ∫⁻ a, partialCubeControl
          (fun z ↦ seed z+gaussianWaveField V a z) [j] ∂gaussianPairs := by
        rw [lintegral_const_mul' _ _ (by norm_num),lintegral_finsetSum _ (fun j _ ↦ hm j)]
      _ ≤ 2 * ∑ j : Fin 4, 81*ENNReal.ofReal (C+1) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ ↦
          gaussian_partial_control_expectation V seed hV hs hb j))
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring
  rw [← ofReal_integral_eq_lintegral_ofReal
    (gaussianGradientSup_integrable V seed hV hs K)
    (Filter.Eventually.of_forall (fun a ↦ norm_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

end
end Yau.Geometry

end OAI

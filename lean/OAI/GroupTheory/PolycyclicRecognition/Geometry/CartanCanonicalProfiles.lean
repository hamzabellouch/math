import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSamplingMean
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfilePointwiseBounds

namespace OAI

/-! # Actual profiles indexed by a real physical scale -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

def CartanFactorModel.realScaleProfile
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (k : F.N.carrier) : C((Fin (finrank ℝ H) → ℝ), W) :=
  rescaledContinuousProfile J hJ x (F.inclusionN k) (max (Real.log r) 0)
    (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
    (F.continuous_profileChart hD _)

@[simp] theorem CartanFactorModel.realScaleProfile_apply
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (k : F.N.carrier) (z : Fin (finrank ℝ H) → ℝ) :
    F.realScaleProfile hD J hJ x X S β r k z =
      rescaledMapProfile J x (F.inclusionN k) (max (Real.log r) 0)
        (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0))) z := rfl

/-- A normalized suffix bound gives the same bound on the mean offset. -/
theorem CartanFactorModel.realScaleProfile_mean_norm_le
    [IsIsometricSMul G G]
    (hD : Continuous F.ExpD) (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r C : ℝ} (hr : 1 ≤ r) (μ : ProbabilityMeasure F.N.carrier)
    (hbound : ∀ᵐ k ∂(μ : Measure F.N.carrier), dist 1 (F.inclusionN k) / r ≤ C) :
    ‖∫ k, F.realScaleProfile hD J hJ.continuous x X S β r k 0
      ∂(μ : Measure F.N.carrier)‖ ≤ (K : ℝ) * C := by
  have hnorm : ∀ᵐ k ∂(μ : Measure F.N.carrier),
      ‖F.realScaleProfile hD J hJ.continuous x X S β r k 0‖ ≤ (K : ℝ) * C := by
    filter_upwards [hbound] with k hk
    have hh := rescaledMapProfile_zero_norm_le hJ x (F.inclusionN k) (max (Real.log r) 0)
      (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
      (by simp [CartanFactorModel.profileChart, F.isExpD.map_zero])
    rw [max_eq_left (Real.log_nonneg hr), Real.exp_log (zero_lt_one.trans_le hr)] at hh
    simpa only [realScaleProfile_apply, max_eq_left (Real.log_nonneg hr)] using
      hh.trans (mul_le_mul_of_nonneg_left hk K.coe_nonneg)
  simpa [measureReal_def] using norm_integral_le_of_norm_le_const hnorm

end PolycyclicRecognition

end

end OAI

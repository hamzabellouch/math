import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereHeat
import OAI.Probability.Perceptron.Variational.GaussianBackward
import OAI.Probability.Perceptron.Variational.AmplitudeConvex

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def cascadeHeatWord (σ : ℕ → ℝ) : (k : ℕ) → (Fin k → ℝ) → List (ℝ×ℝ)
  | 0, _ => []
  | k+1, z => (z 0,σ k)::cascadeHeatWord σ k (fun i => z i.succ)

lemma cascadeHeatWord_nonneg (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ cascadeHeatWord σ k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [cascadeHeatWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

def coordinateDepthField (d j : ℕ) (x : Fin d → ℕ → ℝ) : Spin d :=
  WithLp.toLp 2 (fun i => x i j)

lemma coordinateDepthField_step (d j : ℕ) (σ : ℕ → ℝ)
    (x : Fin d → ℕ → ℝ) (g : Fin d → ℝ) :
    coordinateDepthField d j (canonicalCoordinateStep d σ (x,g))=
      coordinateDepthField d (j+1) x+σ j • WithLp.toLp 2 g := by
  rfl

lemma integral_pi_standardGaussian (d : ℕ) {F : Spin d → ℝ} (hF : Continuous F) :
    (∫ g, F (WithLp.toLp 2 g) ∂(piMarkLaw (fun _ : Fin d => standardGaussianMark) : Measure (Fin d → ℝ)))=
      ∫ y, F y ∂stdGaussian (Spin d) := by
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable]
  rfl

lemma integrable_pi_standardGaussian (d : ℕ) {F : Spin d → ℝ} (hF : Continuous F)
    (hI : Integrable F (stdGaussian (Spin d))) :
    Integrable (fun g => F (WithLp.toLp 2 g))
      (piMarkLaw (fun _ : Fin d => standardGaussianMark)) := by
  rw [← map_pi_eq_stdGaussian] at hI
  exact (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mp hI

lemma coordinateRecursion_eq_backward (d : ℕ) (σ : ℕ → ℝ)
    {f : Spin d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) k z (fun x => f (coordinateLeafField d x)) x=
        gaussianBackward (stdGaussian (Spin d)) (cascadeHeatWord σ k z) f (coordinateDepthField d k x)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) (fun x => f (coordinateLeafField d x)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hl := gaussianBackward_lipschitz (stdGaussian (Spin d)) hf
      (cascadeHeatWord σ k (fun i => z i.succ))
      (cascadeHeatWord_nonneg σ k _ (fun i => (hz i.succ).le))
    let g := gaussianBackward (stdGaussian (Spin d)) (cascadeHeatWord σ k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := hl
    have hcont (x : Fin d → ℕ → ℝ) : Continuous (fun y : Spin d =>
        Real.exp (z 0*g (coordinateDepthField d (k+1) x+σ k • y))) := by
      exact Real.continuous_exp.comp (continuous_const.mul (hg.continuous.comp
        (continuous_const.add (continuous_id.const_smul (σ k)))))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,coordinateDepthField_step,
        cascadeHeatWord,gaussianBackward]
      rw [gaussianEntropic_pos _ hg (hz 0).ne']
      exact congrArg (fun t : ℝ => Real.log t / z 0) (integral_pi_standardGaussian d (hcont x))
    · constructor
      · intro x
        simp only [H.1,coordinateDepthField_step]
        exact integrable_pi_standardGaussian d (hcont x)
          (gaussian_integrable_exp_lipschitz (stdGaussian (Spin d)) hg (z 0) (σ k)
            (coordinateDepthField d (k+1) x))
      · exact H.2

lemma decoratedAngularFactor_eq_terminal_log (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p R).toReal=
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (fun x => logSphericalExp n R (coordinateLeafField (n+1) x)) k p := by
  rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable (n+1) σ) _
    (coordinateLeafField_measurable (n+1))]
  unfold decoratedTerminalTotal
  rw [← decoratedLeafIntegral_exp]
  congr 2
  funext x
  rw [logSphericalExp,Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n _ R))]

lemma coordinateAngularLog_conditional_expectation (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (x : Fin (n+1) → ℕ → ℝ) :
    (∫ η, coordinateAngularLog n k σ R (x,η)
      ∂decoratedCascadeLaw (piMarkLaw (fun _ : Fin (n+1) => standardGaussianMark)) k z)=
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n R) (coordinateDepthField (n+1) k x) := by
  have H := coordinateRecursion_eq_backward (n+1) σ (logSphericalExp_lipschitz n R) k z hz0
  simp only [coordinateAngularLog,decoratedAngularFactor_eq_terminal_log]
  exact (finiteCascade_terminal_log_recursion_of_fractional _ _
    (canonicalCoordinateStep_measurable (n+1) σ) k z hz hz0 hz1
    ((logSphericalExp_lipschitz n R).continuous.measurable.comp
      (coordinateLeafField_measurable (n+1))) H.2 x).trans (H.1 x)

lemma amplitudeSphereValue_eq_backward (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    amplitudeSphereValue n k σ z r=
      gaussianBackward (stdGaussian (Spin (n+1))) ((0,r)::cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) 0/(n+1:ℕ) := by
  have hl := gaussianBackward_lipschitz (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) (cascadeHeatWord σ k z)
    (cascadeHeatWord_nonneg σ k z (fun i => (hz0 i).le))
  unfold amplitudeSphereValue coordinateCascadeLaw
  rw [integral_prod _ (amplitudeSphereLog_integrable n k σ z hz hz0 hz1 r)]
  simp only [amplitudeSphereLog,integral_div,coordinateAngularLog_conditional_expectation n k σ
    (Real.sqrt (n+1:ℕ)) z hz hz0 hz1]
  rw [gaussianBackward,gaussianEntropic_zero _ hl]
  simp only [zero_add]
  congr 1
  exact integral_pi_standardGaussian (n+1) (hl.continuous.comp (continuous_id.const_smul r))

end SphericalPerceptronFreeEnergy
end

end OAI

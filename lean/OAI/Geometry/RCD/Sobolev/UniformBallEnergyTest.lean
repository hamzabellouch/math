import OAI.Geometry.RCD.Sobolev.UniformDensityEnergyTest
import OAI.Geometry.RCD.Metric.EuclideanBallDensityLaw
import OAI.Geometry.RCD.Coordinates.EuclideanDensityNormalization
import OAI.Geometry.RCD.Transport.TranslatedCouplingCost

namespace OAI

/-! # Actual RCD energy controls translated Euclidean ball averages -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_ball_energy_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (ν : FiniteMeasure (Euclidean n))
    (henergy : Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
      (closedBall (p k) (R*r k))
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))).map (v k)) atTop (𝓝 ν))
    (z h : Euclidean n) {a b B : ℝ} (ha : 0<a) (hab : a<b)
    (hinside : ‖z‖+b+‖h‖<ρ) (hB : b+‖h‖<B)
    (hroom : τ+2*(b+‖h‖)<S) (hzR : ‖z‖+(b+‖h‖)<R) :
    ((∫ y, g y ∂(euclideanBallDensityLaw (z+h) ha hab : Measure (Euclidean n)))-
      (∫ y, g y ∂(euclideanBallDensityLaw z ha hab : Measure (Euclidean n))))^2≤
        Real.exp ((n:ℝ)*4*(b+‖h‖))*(‖h‖^2*(volume.real (ball (0:Euclidean n) S)/volume.real (ball z a))*
          (ν : Measure (Euclidean n)).real (closedBall z B)) := by
  let A := euclideanBallDensity z a b hab
  let C := euclideanBallDensity (z+h) a b hab
  have hb : 0<b := ha.trans hab
  have hρS : ρ<S := hρτ.trans (hτR.trans hRS)
  have hzero (x : Euclidean n) (hx : ρ≤‖x‖) : A x=0 := by
    apply euclideanBallDensity_zero z hab
    have ht : ‖x‖≤dist x z+‖z‖ := by simpa only [dist_zero_right] using dist_triangle x z 0
    nlinarith [norm_nonneg h]
  have hzeroC (x : Euclidean n) (hx : ρ≤‖x‖) : C x=0 := by
    apply euclideanBallDensity_zero (z+h) hab
    have ht : ‖x‖≤dist x (z+h)+‖z+h‖ := by simpa only [dist_zero_right] using dist_triangle x (z+h) 0
    have hh := norm_add_le z h
    nlinarith
  have hglobalA : ∀ x, x∉ball (0:Euclidean n) S → A x=0 := by
    intro x hx
    apply hzero
    have hx' : S≤‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
    exact hρS.le.trans hx'
  have hglobalC : ∀ x, x∉ball (0:Euclidean n) S → C x=0 := by
    intro x hx
    apply hzeroC
    have hx' : S≤‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
    exact hρS.le.trans hx'
  let V := volume.real (ball (0:Euclidean n) S)
  have hV : 0<V := ENNReal.toReal_pos
    (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hmA : (∫ x, A x ∂(euclideanBallProbability n S : Measure (Euclidean n)))=
      V⁻¹*(∫ x, A x) := by
    rw [euclideanBallProbability_integral hS,
      setIntegral_eq_integral_of_forall_compl_eq_zero hglobalA]
  have hmC : (∫ x, C x ∂(euclideanBallProbability n S : Measure (Euclidean n)))=
      V⁻¹*(∫ x, A x) := by
    rw [euclideanBallProbability_integral hS,
      setIntegral_eq_integral_of_forall_compl_eq_zero hglobalC]
    congr 1
    calc
      (∫ x, C x) = (∫ x, A (x-h)) := by
        exact integral_congr_ae (Eventually.of_forall fun x => euclideanBallDensity_translate z h x hab)
      _ = _ := integral_sub_right_eq_self A h
  have hpos : 0<∫ x, A x := euclideanBallDensity_mass_pos z ha hab
  have hposA : 0<∫ x, A x ∂(euclideanBallProbability n S : Measure (Euclidean n)) := by
    rw [hmA]; positivity
  have hposC : 0<∫ x, C x ∂(euclideanBallProbability n S : Measure (Euclidean n)) := by
    rw [hmC]; positivity
  have haz (y : Euclidean n) (hy : y∉closedBall z (b+‖h‖)) : A y=0 := by
    apply euclideanBallDensity_zero z hab
    have ht : b+‖h‖<dist y z := lt_of_not_ge hy
    linarith [norm_nonneg h]
  have hcz (y : Euclidean n) (hy : y∉closedBall z (b+‖h‖)) : C y=0 := by
    apply euclideanBallDensity_zero (z+h) hab
    have ht : b+‖h‖<dist y z := lt_of_not_ge hy
    have hd := dist_triangle y (z+h) z
    have he : dist (z+h) z=‖h‖ := by simp [dist_eq_norm]
    rw [he] at hd
    linarith
  obtain ⟨Q,hQ,hbound⟩ := hX.uniform_interior_density_energy_test hn hS hτ hρτ (by positivity) hroom hτR hRS hB z hzR
    p r ε v hr hcurv hε hε1 hεlim hv w g hg hconv ν henergy
    A C (euclideanBallDensity_nonneg z hab) (euclideanBallDensity_nonneg (z+h) hab)
    hzero hzeroC haz hcz hposA hposC
  have hprobA := euclidean_density_inside hS A (euclideanBallDensity_nonneg z hab)
    (euclideanBallDensity_integrable z hab) hglobalA hpos hposA
  have hprobC := euclidean_density_inside hS C (euclideanBallDensity_nonneg (z+h) hab)
    (euclideanBallDensity_integrable (z+h) hab) hglobalC
    (euclideanBallDensity_mass_pos (z+h) ha hab) hposC
  rw [hprobA,hprobC] at hQ hbound
  have hcost := optimal_translation_cost_le (euclideanBallDensityLaw z ha hab) h Q (by
    rw [← euclideanBallDensityLaw_translate]
    exact hQ)
  have hm : 0<volume.real (ball z a) := ENNReal.toReal_pos
    (measure_ball_pos volume z ha).ne' measure_ball_ne_top
  have hmass : volume.real (ball z a)≤∫ x, A x := euclideanBallDensity_mass_lower z hab
  have hcap : max ((∫ y, A y ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖A‖)
      ((∫ y, C y ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖C‖)≤
      V/volume.real (ball z a) := by
    rw [hmA,hmC]
    apply max_le
    all_goals
      calc (V⁻¹*(∫ x, A x))⁻¹*_ ≤ (V⁻¹*(∫ x, A x))⁻¹*1 :=
          mul_le_mul_of_nonneg_left (euclideanBallDensity_norm_le _ hab) (by positivity)
        _ = V/(∫ x, A x) := by field_simp
        _ ≤ V/volume.real (ball z a) := div_le_div_of_nonneg_left hV.le hm hmass
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hcost (mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _))
      (mul_nonneg (Real.exp_nonneg _) (le_max_of_le_left (by positivity))) (sq_nonneg ‖h‖))
    ENNReal.toReal_nonneg)
  dsimp only [V] at hbound'
  convert hbound' using 1
  · rfl
  · ring

end RegularPointCoordinates

end

end OAI

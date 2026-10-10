import OAI.Geometry.RCD.Coordinates.NormalizedLocalEnergy
import OAI.Geometry.RCD.Sobolev.WeakFiniteDomination
import OAI.Geometry.RCD.Metric.PointedMeasureValues

namespace OAI

/-! # Weak limits of the actual normalized local Sobolev energies -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.pointed_energy_subsequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S R M : ℝ} (hS : 0<S) (hR : 0≤R) (hRS : R<S)
    (hM : 0≤M) (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hb : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M) :
    ∃ ν : FiniteMeasure (Euclidean n), ∃ t : ℕ → ℕ, StrictMono t ∧
      Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w (t k))
        (closedBall (p (t k)) (R*r (t k)))
        (r (t k)^2/(hausdorff n X).real (ball (p (t k)) (S*r (t k))))).map (v (t k)))
        atTop (𝓝 ν) ∧
      (ν : Measure (Euclidean n))≤ENNReal.ofReal M •
        (euclideanBallProbability n S : Measure (Euclidean n)) := by
  let μ := hausdorff n X
  let : Nonempty X := ⟨p 0⟩
  let A := fun k => closedBall (p k) (R*r k)
  let U := fun k => ball (p k) (S*r k)
  let E := fun k => localEnergyMeasure μ hX.quadratic (w k) (A k) (r k^2/μ.real (U k))
  let νs := fun k => (E k).map (v k)
  let laws := fun k => normalizedBallPushforward μ (p k) (r k) S (v k)
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hpos (k : ℕ) : 0<μ.real (U k) := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hle (k : ℕ) : (νs k : Measure (Euclidean n))≤
      ENNReal.ofReal M • (laws k : Measure (Euclidean n)) := by
    let : IsFiniteMeasure (μ.restrict (U k)) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (U k) isBounded_ball⟩
    have hAU : A k⊆U k := closedBall_subset_ball (mul_lt_mul_of_pos_right hRS (hr k))
    have he := normalized_local_energy_le μ hX.quadratic (w k) hAU
      (hX.finiteOnBounded _ isBounded_ball).ne (hpos k) (r k) M hM (hb k)
    have hh := Measure.map_mono he (hv k).measurable
    rw [Measure.map_smul _ (hv k).measurable.aemeasurable] at hh
    exact hh
  have hmass (k : ℕ) : (νs k).mass≤M.toNNReal := by
    have hh := hle k univ
    have hm' : ((νs k).mass : ℝ≥0∞)≤ENNReal.ofReal M := by
      simpa only [FiniteMeasure.ennreal_mass,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using hh
    change ((νs k).mass : ℝ≥0∞)≤(M.toNNReal : ℝ≥0∞) at hm'
    exact ENNReal.coe_le_coe.mp hm'
  have hs (k : ℕ) : ∀ᵐ z ∂(νs k : Measure (Euclidean n)), z∈closedBall 0 (R+2) := by
    change ∀ᵐ z ∂(E k : Measure X).map (v k), z∈closedBall 0 (R+2)
    apply (ae_map_iff (hv k).measurable.aemeasurable measurableSet_closedBall).mpr
    have hA := (localEnergyMeasure_absolutelyContinuous μ hX.quadratic (w k) (A k)
      (r k^2/μ.real (U k))).ae_le (ae_restrict_mem measurableSet_closedBall)
    filter_upwards [hA] with x hx
    have hd := (abs_le.mp (pointed_radial_distance (hr k) (hR.trans hRS.le) (hv k).metric
      (hx.trans (mul_le_mul_of_nonneg_right hRS.le (hr k).le)))).2
    have hx' := (div_le_iff₀ (hr k)).mpr hx
    rw [dist_zero_right]
    linarith [hε1 k]
  obtain ⟨ν,t,ht,hlim,_,_⟩ := euclidean_finite_measure_subsequence νs M.toNNReal (R+2) hmass hs
  refine ⟨ν,t,ht,hlim,?_⟩
  have hlaws := measured_approximation_laws_tendsto hS hv
    (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne) hpos hεlim
  have hlawsf := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto
    (euclideanBallProbability n S) |>.comp (hlaws.comp ht.tendsto_atTop)
  exact euclidean_finite_weak_domination (νs ∘ t) (fun k => (laws (t k)).toFiniteMeasure)
    ν (euclideanBallProbability n S).toFiniteMeasure hlim hlawsf
    (fun _ => M.toNNReal) M.toNNReal tendsto_const_nhds (fun k => hle (t k))

end RegularPointCoordinates

end

end OAI

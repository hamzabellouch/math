import OAI.Probability.PosteriorReplicas.Gaussian.ConstrainedNoise
import OAI.Probability.PosteriorReplicas.Measures.EqualApproximation

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev RightSource (d k m : ℕ) := Tuple d m × Rows d k

def rightBaseSource (d k m : ℕ) (base : BaseLaw) : Measure (RightSource d k m) :=
  (Measure.pi (fun _ : Fin (m+1) => base.measure d)).prod (gaussianRows d k)

instance {d k m : ℕ} [NeZero d] (base : BaseLaw) :
    IsProbabilityMeasure (rightBaseSource d k m base) := by
  unfold rightBaseSource
  infer_instance

def equalConstant (k m : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ (-(k * m : ℝ) / 2))

def rightBaseWeight {d k m : ℕ} (z : RightSource d k m) : ℝ≥0∞ :=
  equalConstant k m * (ENNReal.ofReal (affineVolume z.1))⁻¹ ^ k

def residualRows {d k m : ℕ} (u : Tuple d m) (A : Rows d k) : Rows d k :=
  fun j => kernelComponent (differences u) (A j)

def rightBasePoint {d k m : ℕ} (z : RightSource d k m) : EqualSpace d k m :=
  (residualRows z.1 z.2, labels (residualRows z.1 z.2) (z.1 0), z.1)

@[fun_prop] lemma measurable_residualRows {d k m : ℕ} :
    Measurable (fun z : RightSource d k m => residualRows z.1 z.2) := by
  unfold residualRows
  fun_prop

@[fun_prop] lemma measurable_rightBasePoint {d k m : ℕ} :
    Measurable (@rightBasePoint d k m) := by unfold rightBasePoint; fun_prop

@[fun_prop] lemma measurable_rightBaseWeight {d k m : ℕ} :
    Measurable (@rightBaseWeight d k m) := by unfold rightBaseWeight; fun_prop

def rightBaseMeasure (d k m : ℕ) (base : BaseLaw) : Measure (EqualSpace d k m) :=
  ((rightBaseSource d k m base).withDensity rightBaseWeight).map rightBasePoint

lemma rightBaseWeight_integral_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) : (∫⁻ z, rightBaseWeight z ∂rightBaseSource d k m base) < ∞ := by
  have : NeZero d := ⟨by omega⟩
  unfold rightBaseSource rightBaseWeight
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (by unfold equalConstant; finiteness) (base_tuple_inverse_finite hd hm base)

lemma rightBaseMeasure_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) : IsFiniteMeasure (rightBaseMeasure d k m base) := by
  have := isFiniteMeasure_withDensity (rightBaseWeight_integral_finite hd hm base).ne
  unfold rightBaseMeasure
  infer_instance

lemma rightBaseMeasure_lintegral {d k m : ℕ} [NeZero d] (base : BaseLaw)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂rightBaseMeasure d k m base =
      ∫⁻ u : Tuple d m, equalConstant k m * (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
        ∂Measure.pi (fun _ => base.measure d) := by
  rw [rightBaseMeasure, lintegral_map hH measurable_rightBasePoint,
    lintegral_withDensity_eq_lintegral_mul _ measurable_rightBaseWeight
      (show Measurable (fun z => H (rightBasePoint z)) by fun_prop)]
  change (∫⁻ z, rightBaseWeight z * H (rightBasePoint z) ∂rightBaseSource d k m base) = _
  unfold rightBaseSource rightBaseWeight rightBasePoint
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro u
  dsimp only [Prod.fst,Prod.snd]
  rw [lintegral_const_mul _ (by fun_prop)]

lemma constrainedRows_eq_residualRows {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    constrainedRows k u = (gaussianRows d k).map (residualRows u) := by
  unfold constrainedRows residualRows differenceSpan
  simp_rw [kernelComponent_eq_starProjection hu]

lemma constrainedRows_eq_gaussianResidualRows {d k m : ℕ} (u : Tuple d m) :
    constrainedRows k u = gaussianResidualRows (differences u) k := by
  unfold constrainedRows gaussianRows gaussianResidualRows differenceSpan
  exact Measure.pi_map_pi (fun _ => (show Measurable
    (Submodule.span ℝ (range (differences u)))ᗮ.starProjection by fun_prop).aemeasurable)

lemma rows_pairingsDensity_differences {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    (∏ _j : Fin k, pairingsDensity (differences u) 0) =
      equalConstant k m * (ENNReal.ofReal (affineVolume u))⁻¹ ^ k := by
  exact rows_pairingsDensity_zero hu k

lemma rightBaseMeasure_eq_equalLabelRight {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    (base : BaseLaw) {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂rightBaseMeasure d k m base = equalLabelRight base (fun _ => 1) H := by
  have : NeZero d := ⟨by omega⟩
  rw [rightBaseMeasure_lintegral base hH]
  unfold equalLabelRight
  simp only [show (fun _ : Vec d => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_base_tuple_full_rank hd hm base] with u hu
  rw [constrainedRows_eq_residualRows hu, lintegral_map (by fun_prop) (by unfold residualRows; fun_prop)]
  rw [mul_assoc]
  rfl

lemma equalApprox_right_limit {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Continuous H)
    (b : ℝ≥0∞) (hb : b ≠ ∞) (hHb : ∀ x, H x ≤ b) :
    Tendsto (fun n => equalApprox base n H) atTop
      (nhds (∫⁻ z, H z ∂rightBaseMeasure d k m base)) := by
  have : NeZero d := ⟨by omega⟩
  have he (n) : equalApprox base n H =
      ∫⁻ u : Tuple d m, ∫⁻ A, matrixNoiseDensity m k n (fun i j => ⟪differences u i, A j⟫) *
        H (A, labels A (u 0), u) ∂gaussianRows d k ∂Measure.pi (fun _ => base.measure d) := by
    unfold equalApprox
    rw [lintegral_lintegral_swap (by fun_prop)]
    congr 1
    funext u
    congr 1
    funext A
    congr 2
    funext i j
    simp only [labels, differences, Pi.sub_apply, inner_sub_left, real_inner_comm]
  simp_rw [he]
  rw [rightBaseMeasure_lintegral base hH.measurable]
  apply tendsto_lintegral_of_dominated_convergence (fun u : Tuple d m =>
    equalConstant k m * (ENNReal.ofReal (affineVolume u))⁻¹ ^ k * b)
  · intro n
    unfold differences
    fun_prop
  · intro n
    filter_upwards [ae_base_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base] with u hu
    rw [← rows_pairingsDensity_differences hu]
    exact constrained_gaussian_noise_bound hu k n (by unfold labels; fun_prop) b (fun A => hHb _)
  · rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (base_tuple_inverse_finite hd hm base).ne) hb
  · filter_upwards [ae_base_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base] with u hu
    have hlim := constrained_gaussian_noise_limit hu k
      (g := fun A => H (A, labels A (u 0), u)) (by unfold labels; fun_prop) b hb (fun A => hHb _)
    rw [rows_pairingsDensity_differences hu, ← constrainedRows_eq_gaussianResidualRows,
      constrainedRows_eq_residualRows hu, lintegral_map (by fun_prop) (by unfold residualRows; fun_prop)] at hlim
    exact hlim

end PosteriorReplicas
end

end OAI

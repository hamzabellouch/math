import OAI.Probability.PosteriorReplicas.Geometry.BaseGeometry
import OAI.Probability.PosteriorReplicas.Geometry.SphereDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

instance baseLaw_probability (base : BaseLaw) (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (base.measure d) := by
  cases base
  · change IsProbabilityMeasure (PosteriorRegression.ambientSphereLaw (E := Vec d))
    infer_instance
  · change IsProbabilityMeasure (stdGaussian (Vec d))
    infer_instance

@[fun_prop] lemma measurable_baseDensity {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : Rows d k × Labels k => baseDensity base z.1 z.2) := by
  have hLI : MeasurableSet {z : Rows d k × Labels k | LinearIndependent ℝ z.1} := by
    simp_rw [← Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact (measurableSet_eq_fun ((continuous_rowGram.comp continuous_fst).matrix_det.measurable)
      measurable_const).compl
  unfold baseDensity
  apply Measurable.ite hLI
  · cases base
    · exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
        (by fun_prop) measurable_const
    · fun_prop
  · exact measurable_const

@[fun_prop] lemma measurable_projectedDensity {d k : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Rows d k × Labels k => projectedDensity base f z.1 z.2) :=
  (measurable_baseDensity base).mul (measurable_tiltMass base hf)

lemma baseDensity_lt_top {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    baseDensity base A y < ∞ := by
  cases base <;> dsimp only [baseDensity] <;> split_ifs <;> simp

lemma baseDensity_spherical {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) : baseDensity .spherical A y = sphericalPairingsDensity A y := by
  simp only [baseDensity, ite_eq_left hA, sphericalPairingsDensity,
    finrank_euclideanSpace, Fintype.card_fin]
  rfl

lemma base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {g : Vec d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂base.measure d = ∫⁻ y, baseDensity base A y *
      ∫⁻ x, g x ∂baseFiber base A y := by
  simp_rw [baseFiber_eq_map, lintegral_map hg (measurable_basePoint_fixed base A _)]
  cases base
  · change (∫⁻ x, g x ∂uniformDirection (Vec d)) = _
    rw [sphere_fiber_integral hA (by simpa using hk) hg]
    apply lintegral_congr
    intro y
    rw [baseDensity_spherical hA]
    congr 1
    apply lintegral_congr
    intro x
    congr 1
    simp only [basePoint, kernelComponent_eq_starProjection hA, normalDirection,
      smul_smul, div_eq_mul_inv]
    rfl
  · change (∫⁻ x, g x ∂stdGaussian (Vec d)) = _
    rw [gaussian_fiber_integral hA hg]
    apply lintegral_congr
    intro y
    rw [baseDensity, ite_eq_left hA]
    congr 1
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    apply lintegral_congr
    intro x
    rw [basePoint, kernelComponent_eq_starProjection hA]
    rfl

lemma weighted_base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f g : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(base.measure d).withDensity f =
      ∫⁻ y, baseDensity base A y * ∫⁻ x, f x * g x ∂baseFiber base A y := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
  exact base_lintegral hA hk base (hf.mul hg)

lemma tiltMass_le {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) : tiltMass base f A y ≤ L := by
  unfold tiltMass
  calc
    _ ≤ ∫⁻ _, L ∂baseFiber base A y := lintegral_mono hL
    _ = L := by simp

lemma tiltMass_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    tiltMass base f A y ≠ ∞ := ne_top_of_le_ne_top hL (tiltMass_le base hfL A y)

lemma projectedDensity_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    projectedDensity base f A y ≠ ∞ :=
  ENNReal.mul_ne_top (baseDensity_lt_top base A y).ne (tiltMass_ne_top base hL hfL A y)

lemma weighted_fiber_labels {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {g : Labels k → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, f x * g (labels A x) ∂baseFiber base A y = tiltMass base f A y * g y := by
  have hfg : Measurable (fun x => f x * g (labels A x)) := by fun_prop
  rw [baseFiber_eq_map, lintegral_map hfg (measurable_basePoint_fixed base A y)]
  simp_rw [labels_basePoint hA]
  rw [lintegral_mul_const _ (show Measurable (fun x => f (basePoint base A y x)) from
    hf.comp (measurable_basePoint_fixed base A y))]
  congr 1
  rw [tiltMass, baseFiber_eq_map, lintegral_map hf (measurable_basePoint_fixed base A y)]

lemma projected_measure {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    ((base.measure d).withDensity f).map (labels A) =
      volume.withDensity (projectedDensity base f A) := by
  have hl : Measurable (labels A) := by unfold labels; fun_prop
  have hp0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hp0
  have hp : Measurable (projectedDensity base f A) := hp0
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hl]
  rw [weighted_base_lintegral hA hk base hf (g := fun x => g (labels A x)) (hg.comp hl)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hp hg]
  simp only [Pi.mul_apply, weighted_fiber_labels hA base _ hf hg, projectedDensity, mul_assoc]

end PosteriorReplicas
end

end OAI

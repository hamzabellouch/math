import OAI.Probability.PosteriorReplicas.Measures.EqualLabelVersions

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def equalReference {d k m : ℕ} (ν : Measure (Vec d)) : Measure (EqualSpace d k m) :=
  ((Measure.pi (fun _ : Fin (m+1) => ν)).prod (gaussianRows d k)).map rightBasePoint

instance {d k m : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (equalReference (k := k) (m := m) ν) := by
  unfold equalReference
  infer_instance

instance {d k m : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] :
    IsFiniteMeasure (equalReference (k := k) (m := m) ν) := by
  unfold equalReference
  infer_instance

def replicaDensity {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (z : EqualSpace d k m) : ℝ≥0∞ :=
  equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹ ^ k *
    (projectedDensity base f z.1 z.2.1)⁻¹ ^ m

@[fun_prop] lemma measurable_replicaDensity {d k m : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) : Measurable (@replicaDensity d k m base f) := by
  unfold replicaDensity
  fun_prop

def replicaLaw {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞) : Measure (EqualSpace d k m) :=
  (equalReference ((base.measure d).withDensity f)).withDensity (replicaDensity base f)

lemma equalReference_lintegral {d k m : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂equalReference ν = ∫⁻ u : Tuple d m, ∫⁻ A,
      H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
      ∂Measure.pi (fun _ => ν) := by
  rw [equalReference, lintegral_map hH measurable_rightBasePoint,
    lintegral_prod _ (show AEMeasurable (fun z => H (rightBasePoint z)) _ from
      (hH.comp measurable_rightBasePoint).aemeasurable)]
  rfl

lemma density_power_cancel (m : ℕ) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    a^(m+1) * a⁻¹^m = a := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [pow_succ, mul_comm (a^m) a, mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 ha,
      one_pow, mul_one]

lemma replicaLaw_lintegral {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂replicaLaw base f =
      ∫⁻ A, ∫⁻ y, projectedDensity base f A y *
        ∫⁻ u, H (A,y,u) ∂Measure.pi (fun _ : Fin (m+1) => tiltedFiber base f A y)
        ∂volume ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have hG : Measurable (fun z : EqualSpace d k m =>
      (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by fun_prop
  have he := equal_label_tilt_identity hd hk hm base hf hLt hfL hG
  rw [equalLabelRight_residual (by omega) (by omega) base hf hLt hfL hG] at he
  have hrep : (∫⁻ z, H z ∂replicaLaw base f) = equalLabelLeft base f
      (fun z : EqualSpace d k m => (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by
    rw [he]
    rw [replicaLaw, lintegral_withDensity_eq_lintegral_mul _ (measurable_replicaDensity base hf) hH]
    simp only [Pi.mul_apply]
    rw [equalReference_lintegral (base.measure d |>.withDensity f) (by fun_prop)]
    unfold replicaDensity
    simp only
    rw [← lintegral_const_mul _ (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹^k *
      ∫⁻ A, (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k) by
      unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro u
    rw [← mul_assoc, ← lintegral_const_mul _ (show Measurable (fun A =>
      (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u)) by unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro A
    ring
  rw [hrep]
  unfold equalLabelLeft
  apply lintegral_congr
  intro A
  apply lintegral_congr
  intro y
  dsimp only
  rw [lintegral_const_mul _ (show Measurable (fun u : Tuple d m => H (A,y,u)) by fun_prop),
    ← mul_assoc, density_power_cancel m (projectedDensity_ne_top base hLt hfL A y)]

lemma lintegral_projectedDensity {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, projectedDensity base f A y) = (base.measure d).withDensity f univ := by
  have h := congrArg (fun μ : Measure (Labels k) => μ univ) (projected_measure hA hk base hf)
  rw [Measure.map_apply (by unfold labels; fun_prop) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h.symm

lemma replicaLaw_mass {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    replicaLaw (k := k) (m := m) base f univ = (base.measure d).withDensity f univ := by
  rw [← lintegral_one, replicaLaw_lintegral hd hk hm base hf hLt hfL measurable_const]
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  simp only [lintegral_one, measure_univ, mul_one]
  calc
    _ = ∫⁻ (_ : Rows d k), (base.measure d).withDensity f univ ∂gaussianRows d k := by
      apply lintegral_congr_ae
      filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
      exact lintegral_projectedDensity hA (by omega) base hf
    _ = _ := by simp

lemma replicaLaw_probability {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)] :
    IsProbabilityMeasure (replicaLaw (k := k) (m := m) base f) := by
  constructor
  rw [replicaLaw_mass hd hk hm base hf hLt hfL, measure_univ]

end PosteriorReplicas
end

end OAI

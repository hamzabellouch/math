import OAI.Probability.PosteriorReplicas.Measures.EqualLabelIdentity

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma equalConstant_pos (k m : ℕ) : 0 < equalConstant k m := by
  unfold equalConstant
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

lemma ae_tilt_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hL hfL
  rw [pi_withDensity _ _ (fun _ => hf)]
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_base_tuple_full_rank hd hm base] with u hu
  exact fun _ => hu

lemma equalLabelRight_residual {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelRight base f H = equalConstant k m *
      ∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
        ∂Measure.pi (fun _ => (base.measure d).withDensity f) := by
  unfold equalLabelRight equalConstant
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_tilt_tuple_full_rank hd hm base hf hL hfL] with u hu
  rw [constrainedRows_eq_residualRows hu, lintegral_map (by fun_prop) (by unfold residualRows; fun_prop)]

lemma equal_label_transfer {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {g : Rows d k × Labels k → ℝ≥0∞} (hg : Measurable g)
    (hzero : ∀ A, LinearIndependent ℝ A → ∀ᵐ y ∂volume,
      0 < projectedDensity base f A y → g (A,y) = 0) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, g (A, labels A (u 0)) = 0 := by
  have : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hL hfL
  have he : equalLabelLeft (m := m) base f (fun z => g (z.1,z.2.1)) = 0 := by
    unfold equalLabelLeft
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero A hA] with y hy
    by_cases hp : projectedDensity base f A y = 0
    · simp [hp]
    · simp [hy (pos_iff_ne_zero.mpr hp)]
  rw [equal_label_tilt_identity hd hk hm base hf hL hfL (by fun_prop),
    equalLabelRight_residual (by omega) (by omega) base hf hL hfL (by fun_prop)] at he
  have hint : (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
      ∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k
      ∂Measure.pi (fun _ => (base.measure d).withDensity f)) = 0 :=
    (mul_eq_zero.mp he).resolve_left (equalConstant_pos k m).ne'
  have hzg := (lintegral_eq_zero_iff (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k) by
      unfold residualRows; fun_prop)).mp hint
  filter_upwards [hzg, ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base hf hL hfL]
    with u hgu hu
  have hinn : (∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k) = 0 :=
    (mul_eq_zero.mp hgu).resolve_left
      (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
  rw [constrainedRows_eq_residualRows hu]
  apply (ae_map_iff ((show Measurable (residualRows u) by unfold residualRows; fun_prop).aemeasurable)
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  exact (lintegral_eq_zero_iff (by unfold residualRows; fun_prop)).mp hinn

lemma equal_label_transfer_prop {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {P : Rows d k → Labels k → Prop} (hP : MeasurableSet {z : Rows d k × Labels k | P z.1 z.2})
    (hgood : ∀ A, LinearIndependent ℝ A → ∀ᵐ y ∂volume,
      0 < projectedDensity base f A y → P A y) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, P A (labels A (u 0)) := by
  classical
  let g : Rows d k × Labels k → ℝ≥0∞ := fun z => if P z.1 z.2 then 0 else 1
  have hg : Measurable g := Measurable.ite hP measurable_const measurable_const
  have h := equal_label_transfer hd hk hm base hf hL hfL hg (by
    intro A hA
    filter_upwards [hgood A hA] with y hy
    intro hp
    simp [g, hy hp])
  filter_upwards [h] with u hu
  filter_upwards [hu] with A hA
  by_contra hp
  simp [g, hp] at hA

lemma residualRows_equal_labels {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) (R : Rows d k) (i : Fin (m+1)) :
    labels (residualRows u R) (u i) = labels (residualRows u R) (u 0) := by
  refine Fin.cases rfl (fun i => ?_) i
  ext j
  have h := congrFun (labels_kernelComponent hu (R j)) i
  change ⟪differences u i, kernelComponent (differences u) (R j)⟫ = 0 at h
  rw [real_inner_comm, differences, inner_sub_right] at h
  exact sub_eq_zero.mp h

lemma ae_constrained_equal_labels {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    ∀ᵐ A ∂constrainedRows k u, ∀ i, labels A (u i) = labels A (u 0) := by
  rw [constrainedRows_eq_residualRows hu]
  have hp : Measurable (fun A : Rows d k => ∀ i, labels A (u i) = labels A (u 0)) := by
    unfold labels
    fun_prop
  apply (ae_map_iff ((show Measurable (residualRows u) by unfold residualRows; fun_prop).aemeasurable) hp.setOf).mpr
  exact Filter.Eventually.of_forall (fun R => residualRows_equal_labels hu R)

lemma projectedDensity_positive_sphere {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (A : Rows d k) (y : Labels k) (hp : 0 < projectedDensity base f A y) :
    LinearIndependent ℝ A ∧ (base = .spherical → ‖liftLabel A y‖ < 1) := by
  have hb : baseDensity base A y ≠ 0 := by
    intro hc
    simp [projectedDensity, hc] at hp
  by_cases hA : LinearIndependent ℝ A
  · refine ⟨hA, ?_⟩
    intro hs
    subst base
    by_contra hy
    exact hb (by simp [baseDensity, hA, hy])
  · exact False.elim (hb (by simp [baseDensity, hA]))

lemma ae_constrained_support {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      LinearIndependent ℝ (differences u) ∧
      ∀ᵐ A ∂constrainedRows k u,
        LinearIndependent ℝ A ∧ (∀ i, labels A (u i) = labels A (u 0)) ∧
        (base = .spherical → ‖liftLabel A (labels A (u 0))‖ < 1) ∧
        0 < projectedDensity base f A (labels A (u 0)) ∧
        projectedDensity base f A (labels A (u 0)) ≠ ∞ := by
  have hp := equal_label_transfer_prop hd hk hm base hf hL hfL
    (P := fun A y => 0 < projectedDensity base f A y)
    (measurableSet_lt measurable_const (measurable_projectedDensity base hf))
    (fun A _ => Filter.Eventually.of_forall fun y => id)
  filter_upwards [hp, ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base hf hL hfL]
    with u hu hU
  refine ⟨hU, ?_⟩
  filter_upwards [hu, ae_constrained_equal_labels hU] with A hA heq
  have hsup := projectedDensity_positive_sphere base A (labels A (u 0)) hA
  exact ⟨hsup.1, heq, hsup.2, hA, projectedDensity_ne_top base hL hfL A (labels A (u 0))⟩

end PosteriorReplicas
end

end OAI

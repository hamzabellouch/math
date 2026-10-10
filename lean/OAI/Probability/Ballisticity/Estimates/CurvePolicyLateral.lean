import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicy
import OAI.Probability.Ballisticity.Walk.SelectedKernelMap

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_eq_success_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveIncrement (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict
        (Cross (realPosition (step e)) x H ∩
          {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B})).map
        (fun X => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  rw [curveIncrement,curveEndpoint_eq_map e f x b B hH ω,Measure.map_map]
  · simp only [Function.comp_def,add_sub_cancel_left]
    congr 1
    apply Measure.restrict_congr_set
    simpa only [cross_eq_hit] using curvePrefix_ae_eq e f x b B hH ω
  · exact measurable_of_countable _
  · exact measurable_const.add ((measurable_recordIndexPosition _ _).comp (by fun_prop))

lemma curvePolicy_lateral {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) :
    (curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω).map (signedCoordinate f) =
      selectedEndpointLaw ((quenchedKernel (ω,x))[|Cross (realPosition (step e)) x H])
        {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B}
        ({X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} ∩
          (fun X => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) ⁻¹' E)
        (fun X => signedCoordinate f (recordIndexPosition (realPosition (step e)) H (fun j => X j-x)))
        (signedCoordinate f dummy)
        (curveIncrement (realPosition (step e)) f x b B H ω Set.univ < δ)
        (α * crossingQuenched (realPosition (step e)) x H ω ≤
          curveIncrement (realPosition (step e)) f x b B H ω E) := by
  let ℓ := realPosition (step e)
  let N := {X : Path d | medianDeviation ℓ f b H (fun j => X j-x) ≤ B}
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  have hZ : Measurable Z := (measurable_recordIndexPosition _ _).comp (by fun_prop)
  have hN : MeasurableSet N := measurableSet_le
    ((measurable_medianDeviation ℓ f b H).comp (by fun_prop)) measurable_const
  rw [selectedEndpointLaw_cond _ _ _ _ (measurableSet_cross ℓ x H) hN
    (hN.inter (hZ E.to_countable.measurableSet))]
  change (selectedFiniteKernel _ E dummy _ _).map (signedCoordinate f) = _
  conv_lhs => arg 2; arg 1; rw [curveIncrement_eq_success_map e f x b B hH ω]
  rw [selectedFiniteKernel_map_eq _ _ _ hZ E E.to_countable.measurableSet
    (signedCoordinate f) (measurable_of_countable _) dummy]
  simp only [Set.inter_assoc,Function.comp_def]
  rfl

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveEndpoint_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂curveEndpoint (realPosition (step e)) f x b B H ω,
      signedHeight e y = signedHeight e x+H := by
  rw [ae_iff,curveEndpoint_apply]
  apply ENNReal.tsum_eq_zero.mpr; intro n
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  rintro ⟨hbad,hCurve⟩
  exact hbad (coordinate_hitAt_exact e x X h0 hnn H n hCurve.1)

lemma curveIncrement_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂curveIncrement (realPosition (step e)) f x b B H ω, signedHeight e y = H := by
  rw [curveIncrement,ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _ |>.measurableSet)]
  filter_upwards [curveEndpoint_supported e f x b B H ω] with y hy
  rw [signedHeight_sub,hy]
  omega

lemma selectedFiniteKernel_supported {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] (P : α → Prop)
    (hd : P dummy) (hD : ∀ᵐ u ∂D, P u) :
    ∀ᵐ u ∂selectedFiniteKernel D E dummy failure strict, P u := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,ite_eq_left hf,ae_dirac_eq,Filter.eventually_pure]
    exact hd
  simp only [selectedFiniteKernel,ite_eq_right hf,normalizeFinite]
  rw [ae_iff,Measure.smul_apply,smul_eq_mul]
  have he : ∀ᵐ u ∂(if strict then D.restrict E else D), P u := by
    split_ifs
    · exact hD.filter_mono (ae_mono Measure.restrict_le_self)
    · exact hD
  rw [ae_iff.mp he,mul_zero]

lemma curvePolicy_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (hd : signedHeight e dummy = H) (ω : Environment d) :
    ∀ᵐ y ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
      signedHeight e y = H :=
  selectedFiniteKernel_supported _ _ _ _ _ _ hd (curveIncrement_supported e f x b B H ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    ∀ᵐ u ∂curveIncrement (realPosition (step e)) f x b B H ω,
      |signedCoordinate f u-b H| ≤ B := by
  have hm : Measurable (fun X : Path d => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) :=
    (measurable_recordIndexPosition _ _).comp (by fun_prop)
  rw [curveIncrement_eq_success_map e f x b B hH ω,
    ae_map_iff hm.aemeasurable (Set.to_countable _ |>.measurableSet)]
  filter_upwards [ae_restrict_mem (measurableSet_cross _ _ _ |>.inter
    (measurableSet_le ((measurable_medianDeviation _ f b H).comp (by fun_prop)) measurable_const))]
    with X hX
  exact (medianDeviation_le_iff _ f b H _ B).mp hX.2 H le_rfl

lemma curvePolicy_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) (δ α : ℝ≥0∞) (dummy : Lattice d)
    (hd : signedCoordinate f dummy = b H) (ω : Environment d) :
    ∀ᵐ u ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
      |signedCoordinate f u-b H| ≤ B :=
  selectedFiniteKernel_supported _ _ _ _ _ _ (by simpa [hd] using hB)
    (curveIncrement_lateral_bound e f x b B hH ω)

lemma curvePolicy_square_integrable {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) (ω : Environment d) :
    Integrable (fun u => (signedCoordinate f u-b H)^2)
      (curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω) := by
  have := curvePolicy_probability (realPosition (step e)) f x b B H E hδ hα dummy ω
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (B^2)
  filter_upwards [curvePolicy_lateral_bound e f x b hB hH E δ α dummy hd ω] with u hu
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (signedCoordinate f u-b H))]
  nlinarith [sq_abs (signedCoordinate f u-b H),sq_nonneg (B-|signedCoordinate f u-b H|),
    abs_nonneg (signedCoordinate f u-b H)]

end DirectionalTransience

end

end

end OAI

import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurveEndpointLaw
import OAI.Probability.Ballisticity.Walk.SelectedFiniteKernel

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curveIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  (curveEndpoint ℓ f x b B H ω).map (fun y => y-x)

instance curveIncrement_finite {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    IsFiniteMeasure (curveIncrement ℓ f x b B H ω) := by
  unfold curveIncrement; infer_instance

lemma curveIncrement_total {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω Set.univ = quenchedKernel (ω,x) (CurvePrefix ℓ f x b B H) := by
  rw [curveIncrement,Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ,curveEndpoint_total]

lemma curveIncrement_le_crossing {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω Set.univ ≤ crossingQuenched ℓ x H ω := by
  rw [curveIncrement_total,crossingQuenched,cross_eq_hit]
  apply measure_mono
  intro X hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

lemma curveIncrement_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (curveIncrement ℓ f x b B H) := by
  exact (Measure.measurable_map _ (measurable_of_countable _)).comp (curveEndpoint_rows ℓ f x b B hH)

noncomputable def curvePolicy {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) : Measure (Lattice d) :=
  selectedFiniteKernel (curveIncrement ℓ f x b B H ω) E dummy
    (curveIncrement ℓ f x b B H ω Set.univ < δ)
    (α * crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E)

lemma curvePolicy_probability {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (ω : Environment d) :
    IsProbabilityMeasure (curvePolicy ℓ f x b B H E δ α dummy ω) := by
  apply selectedFiniteKernel_probability
  · intro hf
    exact ne_of_gt (lt_of_lt_of_le hδ (not_lt.mp hf))
  · intro hf hs
    have ha : 0 < crossingQuenched ℓ x H ω :=
      lt_of_lt_of_le (lt_of_lt_of_le hδ (not_lt.mp hf))
        (curveIncrement_le_crossing ℓ f x b B H ω)
    exact ne_of_gt ((ENNReal.mul_pos hα.ne' ha.ne').trans_le hs)

lemma curvePolicy_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (curvePolicy ℓ f x b B H E δ α dummy) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x H)
  have hm := curveIncrement_rows ℓ f x b B hH
  have hc := measurable_crossingQuenched_rows ℓ x (show (0:ℝ)<H by exact_mod_cast hH)
  exact selectedFiniteKernel_measurable _ hm E E.to_countable.measurableSet dummy _ _
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const)
    (measurableSet_le (measurable_const.mul hc)
      ((Measure.measurable_coe E.to_countable.measurableSet).comp hm))

lemma curvePolicy_domination {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d)
    (hf : δ ≤ curveIncrement ℓ f x b B H ω Set.univ) :
    curvePolicy ℓ f x b B H E δ α dummy ω ≤
      (α*δ)⁻¹ • curveIncrement ℓ f x b B H ω := by
  apply selectedFiniteKernel_domination _ _ _ _ _ (mul_ne_zero hα.ne' hδ.ne') (not_lt.mpr hf)
  · exact (mul_le_of_le_one_left' hα1).trans hf
  · intro hs
    apply le_trans ?_ hs
    gcongr
    exact hf.trans (curveIncrement_le_crossing ℓ f x b B H ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω = curveIncrement ℓ f 0 b B H (fun y => ω (x+y)) := by
  unfold curveIncrement
  rw [curveEndpoint_increment_translation]
  simp only [sub_zero]
  exact (Measure.map_id).symm

lemma crossingQuenched_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = crossingQuenched ℓ 0 H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have he := congrArg (fun μ : Measure (Path d) => μ (Cross ℓ 0 H)) (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_cross _ _ _),cross_translation] at he
  simpa only [add_zero,crossingQuenched] using he

lemma curvePolicy_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) :
    curvePolicy ℓ f x b B H E δ α dummy ω =
      curvePolicy ℓ f 0 b B H E δ α dummy (fun y => ω (x+y)) := by
  unfold curvePolicy
  rw [curveIncrement_translation,crossingQuenched_translation]

lemma curvePolicy_annealed_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ)
    {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) (δ α : ℝ≥0∞)
    (dummy : Lattice d) (U : Set (Lattice d)) :
    (∫⁻ ω, curvePolicy ℓ f x b B H E δ α dummy ω U ∂environmentLaw ν) =
      ∫⁻ ω, curvePolicy ℓ f 0 b B H E δ α dummy ω U ∂environmentLaw ν := by
  simp_rw [curvePolicy_translation ℓ f x]
  have hm : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  have hp := ((Measure.measurable_coe U.to_countable.measurableSet).comp
    ((curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl))
  change (∫⁻ ω, ((fun μ => μ U) ∘ curvePolicy ℓ f 0 b B H E δ α dummy)
    ((fun ω : Environment d => fun y => ω (x+y)) ω) ∂environmentLaw ν) = _
  rw [← lintegral_map hp hm,environment_translation]
  rfl

end DirectionalTransience

end

end

end OAI

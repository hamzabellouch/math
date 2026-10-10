import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferStageSuccess
import OAI.Probability.Ballisticity.Estimates.RawPairLocality

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def rawPairMixture {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Measure (Lattice d × Lattice d) :=
  π.bind (rawPairEndpointLaw ℓ H ω)

lemma rawPairMixture_apply {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (U : Set (Lattice d × Lattice d)) :
    rawPairMixture ℓ H π ω U = ∫⁻ x, rawPairEndpointLaw ℓ H ω x U ∂π :=
  Measure.bind_apply (Set.to_countable U).measurableSet (measurable_of_countable _).aemeasurable

lemma rawPairMixture_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    rawPairMixture ℓ H π ω Set.univ ≤ 1 := by
  rw [rawPairMixture_apply]
  calc
    _ ≤ ∫⁻ _ : Lattice d × Lattice d, (1:ℝ≥0∞) ∂π :=
      lintegral_mono fun x => rawPairEndpointLaw_total_le_one ℓ H ω x
    _ = 1 := by simp

noncomputable def retainedPairLaw {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    Measure (Lattice d × Lattice d) :=
  (rawPairMixture ℓ H π ω).restrict {y | z ≤ signedCoordinate f (y.2-y.1)}

lemma retainedPairLaw_mass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f H z π ω Set.univ = pairKernelMass ℓ f H z π ω := by
  rw [retainedPairLaw,Measure.restrict_apply_univ,rawPairMixture_apply]
  rfl

lemma retainedPairLaw_le {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f H z π ω ≤ rawPairMixture ℓ H π ω := Measure.restrict_le_self

lemma retainedPairLaw_support {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    ∀ᵐ y ∂retainedPairLaw ℓ f H z π ω, z ≤ signedCoordinate f (y.2-y.1) :=
  ae_restrict_mem (Set.to_countable _).measurableSet

lemma rawPairMixture_joint_rows {d : ℕ} (ℓ : Vector d)
    {H : ℕ} (hH : 0 < H) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => rawPairMixture ℓ H p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [rawPairMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm : @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞ _ _
        (fun p => rawPairEndpointLaw ℓ H p.2 x U) :=
      ((Measure.measurable_coe hU).comp
        (rawPairEndpointLaw_rows ℓ x hH (hC x hx).1 (hC x hx).2)).comp measurable_snd
    exact hm.mul ((Measure.measurable_coe (measurableSet_singleton x)).comp
      (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedPairMeasures C × Environment d =>
        rawPairEndpointLaw ℓ H p.2 x U*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedPairMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma retainedPairLaw_joint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => retainedPairLaw ℓ f H z p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [retainedPairLaw,Measure.restrict_apply hU]
  exact (Measure.measurable_coe (hU.inter (Set.to_countable _).measurableSet)).comp
    (rawPairMixture_joint_rows ℓ hH C S hC)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_normalizedMeasure {α : Type*} [MeasurableSpace α] :
    Measurable (normalizedMeasure (α := α)) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [normalizedMeasure,Measure.smul_apply,smul_eq_mul]
  exact (Measure.measurable_coe MeasurableSet.univ).inv.mul (Measure.measurable_coe hU)

lemma normalizedMeasure_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : normalizedMeasure μ ≪ μ := by
  intro U hU
  simp only [normalizedMeasure,Measure.smul_apply,hU,mul_zero,smul_eq_mul]

lemma normalized_retainedPair_probability {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) (hg : 0 < pairKernelMass ℓ f H z π ω) :
    IsProbabilityMeasure (normalizedMeasure (retainedPairLaw ℓ f H z π ω)) := by
  let : IsFiniteMeasure (retainedPairLaw ℓ f H z π ω) :=
    ⟨by rw [retainedPairLaw_mass]; exact lt_of_le_of_lt (pairKernelMass_le_one ℓ f H z π ω) ENNReal.one_lt_top⟩
  apply normalizedMeasure_probability
  rw [retainedPairLaw_mass]
  exact hg.ne'

lemma normalized_retainedPair_support {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    ∀ᵐ y ∂normalizedMeasure (retainedPairLaw ℓ f H z π ω), z ≤ signedCoordinate f (y.2-y.1) :=
  (normalizedMeasure_absolutelyContinuous _).ae_le (retainedPairLaw_support ℓ f H z π ω)

lemma normalized_retainedPair_joint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => normalizedMeasure (retainedPairLaw ℓ f H z p.1.val p.2)) :=
  measurable_normalizedMeasure.comp (retainedPairLaw_joint_rows ℓ f hH z C S hC)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def BufferStageEvent {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ)
    (z₀ r ε a g : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Prop :=
  (∀ h : ℕ, 0 < h → h ≤ H → ENNReal.ofReal g ≤ pairKernelMass ℓ f h (z₀+(1-ε)*r) π ω) ∧
    ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+a)*r) π ω

lemma bufferStageEvent_iff {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z₀ r ε a : ℝ) {g : ℝ} (hg : 0 ≤ g) (π : Measure (Lattice d × Lattice d))
    [IsProbabilityMeasure π] (ω : Environment d) :
    BufferStageEvent (realPosition (step e)) f H z₀ r ε a g π ω ↔
      BufferStageSuccess (realPosition (step e)) f H z₀ r ε a g π ω := by
  unfold BufferStageEvent BufferStageSuccess
  apply and_congr
  · apply forall_congr'
    intro h
    apply forall_congr'
    intro hh
    apply forall_congr'
    intro _
    exact pairKernelMass_lower_iff e f hh _ π ω hg
  · exact pairKernelMass_lower_iff e f hH _ π ω hg

lemma strip_mono_nat_height {d : ℕ} (ℓ : Vector d) (x : Lattice d) {h H : ℕ} (hh : h ≤ H) :
    Strip ℓ x h ⊆ Strip ℓ x H := by
  intro y hy
  have hhR : (h:ℝ) ≤ H := by exact_mod_cast hh
  exact ⟨hy.1,by dsimp [Strip] at hy ⊢; linarith [hy.2]⟩

lemma measurableSet_bufferStageEvent_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z₀ r ε a g : ℝ) (C : Set (Lattice d × Lattice d))
    (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @MeasurableSet (SupportedPairMeasures C × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | BufferStageEvent ℓ f H z₀ r ε a g p.1.val p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  unfold BufferStageEvent
  apply MeasurableSet.inter
  · change MeasurableSet {p : SupportedPairMeasures C × Environment d | ∀ h : ℕ, 0 < h → h ≤ H → ENNReal.ofReal g ≤ pairKernelMass ℓ f h (z₀+(1-ε)*r) p.1.val p.2}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro h
    apply MeasurableSet.iInter
    intro hh
    apply MeasurableSet.iInter
    intro hhH
    exact measurableSet_le measurable_const (pairKernelMass_joint_rows ℓ f hh _ C S
      (fun x hx => ⟨(strip_mono_nat_height ℓ x.1 hhH).trans (hC x hx).1,
        (strip_mono_nat_height ℓ x.2 hhH).trans (hC x hx).2⟩))
  · exact measurableSet_le measurable_const (pairKernelMass_joint_rows ℓ f hH _ C S hC)
end DirectionalTransience

end

end

end OAI

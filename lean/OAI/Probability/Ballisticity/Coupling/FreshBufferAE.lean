import Mathlib
import OAI.Probability.Ballisticity.Walk.FreshRowWeights

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairLawValidSet {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) : Set (Environment d) :=
  {ω | (π ω).val Set.univ=1 ∧ (π ω).val {x | ¬ z ≤ signedCoordinate f (x.2-x.1)}=0}

lemma pairLawValidSet_iff {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) (ω : Environment d) :
    ω ∈ pairLawValidSet f z π ↔ IsProbabilityMeasure (π ω).val ∧
      ∀ᵐ x ∂(π ω).val, z ≤ signedCoordinate f (x.2-x.1) := by
  constructor
  · rintro ⟨hp,hg⟩
    exact ⟨⟨hp⟩,ae_iff.mpr hg⟩
  · rintro ⟨hp,hg⟩
    let := hp
    exact ⟨measure_univ,ae_iff.mp hg⟩

lemma pairLawValidSet_measurable {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) {m : MeasurableSpace (Environment d)} (hπ : @Measurable _ _ m _ π) :
    MeasurableSet[m] (pairLawValidSet f z π) := by
  have hm := hπ.subtype_val
  exact (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const).inter
    (measurableSet_eq_fun ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm) measurable_const)

lemma weighted_test_ae_valid {Ω : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (μ : @Measure Ω mΩ) (A V E : Set Ω) (hA : MeasurableSet[m] A)
    (hV : MeasurableSet[m] V) (w : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hvalid : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ V)
    (hbound : ∀ A', MeasurableSet[m] A' → A' ⊆ A → A' ⊆ V →
      c*(∫⁻ ω in A', w ω ∂μ) ≤ ∫⁻ ω in A' ∩ E, w ω ∂μ) :
    c*(∫⁻ ω in A, w ω ∂μ) ≤ ∫⁻ ω in A ∩ E, w ω ∂μ := by
  have hv : (fun ω => ω ∈ A ∩ V) =ᵐ[μ] (fun ω => ω ∈ A) := hvalid.mono fun ω h => by
    simp only [Set.mem_inter_iff]
    exact propext ⟨And.left,fun hA => ⟨hA,h hA⟩⟩
  have hvE : (fun ω => ω ∈ (A ∩ V) ∩ E) =ᵐ[μ] (fun ω => ω ∈ A ∩ E) := hv.mono fun ω h => by
    change (ω ∈ A ∩ V ∧ ω ∈ E) = (ω ∈ A ∧ ω ∈ E)
    change (ω ∈ A ∩ V) = (ω ∈ A) at h
    rw [h]
  have hh := hbound (A ∩ V) (hA.inter hV) Set.inter_subset_left Set.inter_subset_right
  have hr : μ.restrict (A ∩ V)=μ.restrict A := by
    rw [Set.inter_comm, ← Measure.restrict_restrict (hm V hV)]
    exact Measure.restrict_eq_self_of_ae_mem ((ae_restrict_iff' (hm A hA)).mpr hvalid)
  have hrE : μ.restrict ((A ∩ V) ∩ E)=μ.restrict (A ∩ E) := Measure.restrict_congr_set hvE
  rwa [hr,hrE] at hh

lemma fresh_buffer_weight_ae_valid {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) {H : ℕ} (hH : 0 < H) (z₀ r ε α g c : ℝ)
    (C : Set (Lattice d × Lattice d)) (D S : Set (Lattice d))
    (hdis : Disjoint D S) (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S)
    (hchance : ∀ π : SupportedPairMeasures C, IsProbabilityMeasure π.val →
      (∀ᵐ x ∂π.val, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
      ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent ℓ f H z₀ r ε α g π.val ω})
    (π : Environment d → SupportedPairMeasures C)
    (hπ : @Measurable _ _ (rowSigma D) _ π) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma D] A)
    (hvalid : ∀ᵐ ω ∂environmentLaw ν, ω ∈ A → IsProbabilityMeasure (π ω).val ∧
      ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1))
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma D) _ w) :
    ENNReal.ofReal c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω}, w ω ∂environmentLaw ν := by
  apply weighted_test_ae_valid (mΩ := (inferInstance : MeasurableSpace (Environment d))) (m := rowSigma D) (rowSigma_le D) (environmentLaw ν) A (pairLawValidSet f (z₀+r) π)
    {ω | BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω} hA
    (pairLawValidSet_measurable f (z₀+r) π hπ) w (ENNReal.ofReal c)
      (hvalid.mono fun ω h hω => (pairLawValidSet_iff f (z₀+r) π ω).mpr (h hω))
  intro A' hA' hsub hV
  apply fresh_buffer_weighted_test ν ℓ f hH z₀ r ε α g C hdis hC π hπ A' hA' w hw
  intro ω hω
  obtain ⟨hp,hgap⟩ := (pairLawValidSet_iff f (z₀+r) π ω).mp (hV hω)
  exact hchance (π ω) hp hgap
end DirectionalTransience

end

end

end OAI

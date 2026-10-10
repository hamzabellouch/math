import Mathlib
import OAI.Probability.Ballisticity.Entropy.OccupationEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.Entropy
variable {Z F I : Type*} [MeasurableSpace Z] [MeasurableSpace F]

lemma fst_restrict_preimage (μ : Measure (Z × F)) (A : Set Z) (hA : MeasurableSet A) :
    (μ.restrict (Prod.fst ⁻¹' A)).fst = μ.fst.restrict A :=
  (Measure.restrict_map measurable_fst hA).symm

lemma fresh_restrict (ζ : Measure Z) [SFinite ζ] (π : Measure F) [SFinite π] (A : Set Z) :
    (ζ.prod π).restrict (Prod.fst ⁻¹' A) = (ζ.restrict A).prod π := by
  have he : (Prod.fst ⁻¹' A : Set (Z × F)) = A ×ˢ Set.univ := by ext p; simp
  rw [he,← Measure.prod_restrict,Measure.restrict_univ]

lemma fresh_activeSum (s : Finset I) (μ : I → Measure (Z × F))
    [∀ i, IsFiniteMeasure (μ i)] (π : Measure F) [IsProbabilityMeasure π]
    (A : I → Set Z) (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    activeSum s (fun i => (μ i).fst.prod π) (fun i => Prod.fst ⁻¹' A i) =
      (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).fst.prod π := by
  induction s using Finset.induction_on with
  | empty => simp [activeSum,Measure.fst]
  | @insert a s ha ih =>
    have hAa := hA a (Finset.mem_insert_self a s)
    have hAs : ∀ i ∈ s, MeasurableSet (A i) := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    simp only [activeSum,Finset.sum_insert ha] at ih ⊢
    rw [Measure.fst_add,Measure.add_prod,fst_restrict_preimage _ _ hAa,fresh_restrict]
    rw [ih hAs]

lemma fresh_activeMass (μ : Measure (Z × F)) (π : Measure F) [IsProbabilityMeasure π]
    (A : Set Z) (hA : MeasurableSet A) :
    μ (Prod.fst ⁻¹' A) = (μ.fst.prod π) (Prod.fst ⁻¹' A) := by
  rw [← Measure.fst_apply hA, ← Measure.fst_apply hA,Measure.fst_prod]

lemma normalize_fst_prod [Nonempty (Z × F)]
    (μ : FiniteMeasure (Z × F)) (π : Measure F) [IsProbabilityMeasure π]
    (hμ : μ ≠ 0) :
    let ν : FiniteMeasure (Z × F) := ⟨(μ : Measure (Z × F)).fst.prod π,inferInstance⟩
    (ν.normalize : Measure (Z × F)) = (μ.normalize : Measure (Z × F)).fst.prod π := by
  let ν : FiniteMeasure (Z × F) := ⟨(μ : Measure (Z × F)).fst.prod π,inferInstance⟩
  change (ν.normalize : Measure (Z × F)) = (μ.normalize : Measure (Z × F)).fst.prod π
  have hm : ν.mass = μ.mass := by
    change ((μ : Measure (Z × F)).fst.prod π Set.univ).toNNReal = _
    rw [← Set.univ_prod_univ,Measure.prod_prod,measure_univ (μ:=π),mul_one,Measure.fst_univ]
    rfl
  have hν : ν ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff,hm]
    exact μ.mass_nonzero_iff.mpr hμ
  rw [ν.toMeasure_normalize_eq_of_nonzero hν,μ.toMeasure_normalize_eq_of_nonzero hμ,hm]
  change μ.mass⁻¹ • ((μ : Measure (Z × F)).fst.prod π) =
    ((μ.mass⁻¹ • (μ : Measure (Z × F))).map Prod.fst).prod π
  rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.prod_smul_left]
  rfl

theorem own_normalized_activeSum_kl_le [Nonempty (Z × F)]
    (s : Finset I) (μ : I → Measure (Z × F)) [∀ i, IsProbabilityMeasure (μ i)]
    (π : Measure F) [IsProbabilityMeasure π]
    (A : I → Set Z) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hkl : ∀ i ∈ s, klDiv (μ i) ((μ i).fst.prod π) ≠ ∞)
    (hpos : 0 < (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ) :
    let μs : FiniteMeasure (Z × F) := ⟨activeSum s μ (fun i => Prod.fst ⁻¹' A i),inferInstance⟩
    klDiv (μs.normalize : Measure (Z × F)) ((μs.normalize : Measure (Z × F)).fst.prod π) ≤
      ENNReal.ofReal ((∑ i ∈ s, (klDiv (μ i) ((μ i).fst.prod π)).toReal) /
        (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ) := by
  let μs : FiniteMeasure (Z × F) := ⟨activeSum s μ (fun i => Prod.fst ⁻¹' A i),inferInstance⟩
  have hμ : μs ≠ 0 := by
    intro h
    have hz : (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ = 0 := by
      change (μs : Measure (Z × F)).real Set.univ = 0
      rw [h]; simp
    linarith
  have h := normalized_activeSum_kl_le s μ (fun i => (μ i).fst.prod π) hkl
    (fun i => Prod.fst ⁻¹' A i) (fun i hi => (hA i hi).preimage measurable_fst)
    (fun i hi => fresh_activeMass (μ i) π (A i) (hA i hi)) hpos
  let νs : FiniteMeasure (Z × F) := ⟨activeSum s (fun i => (μ i).fst.prod π)
    (fun i => Prod.fst ⁻¹' A i),inferInstance⟩
  let νs' : FiniteMeasure (Z × F) := ⟨(μs : Measure (Z × F)).fst.prod π,inferInstance⟩
  have heq : νs = νs' := by
    apply Subtype.ext
    exact fresh_activeSum s μ π A hA
  change klDiv (μs.normalize : Measure (Z × F)) (νs.normalize : Measure (Z × F)) ≤ _ at h
  rw [heq] at h
  have hnorm : (νs'.normalize : Measure (Z × F)) =
      (μs.normalize : Measure (Z × F)).fst.prod π := normalize_fst_prod μs π hμ
  rw [hnorm] at h
  exact h

end DirectionalTransience.Entropy

end

end OAI

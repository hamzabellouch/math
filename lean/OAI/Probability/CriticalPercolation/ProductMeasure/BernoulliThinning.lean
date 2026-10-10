import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def containsFinite (S : Finset E) : Set (Set E) := {ω | (S : Set E)⊆ω}

lemma measurableSet_containsFinite (S : Finset E) : MeasurableSet (containsFinite S) := by
  have he : containsFinite S=⋂ e∈S, {ω : Set E | e∈ω} := by
    ext ω
    simp [containsFinite,Set.subset_def]
  rw [he]
  exact Finset.measurableSet_biInter _ (fun e _ => (measurable_set_mem e).setOf)

lemma containsFinite_inter (S T : Finset E) :
    containsFinite S∩containsFinite T=containsFinite (S∪T) := by
  ext ω
  simp only [containsFinite,Set.mem_inter_iff,Set.mem_ofPred_eq,Finset.coe_union,
    Set.union_subset_iff]

lemma measure_ext_containsFinite (μ ν : Measure (Set E)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ S : Finset E, μ (containsFinite S)=ν (containsFinite S)) :
    μ=ν := by
  let C : Set (Set (Set E)) := Set.range (containsFinite (E := E))
  have hgen : (inferInstance : MeasurableSpace (Set E))=MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · change (⨆ e : E, MeasurableSpace.comap (fun ω : Set E => e∈ω) inferInstance)≤_
      apply iSup_le
      intro e
      apply measurable_iff_comap_le.mp
      apply measurable_to_prop
      have he : (fun ω : Set E => e∈ω) ⁻¹' {True}=containsFinite {e} := by
        ext ω
        simp [containsFinite]
      rw [he]
      exact MeasurableSpace.measurableSet_generateFrom ⟨{e},rfl⟩
    · apply MeasurableSpace.generateFrom_le
      rintro A ⟨S,rfl⟩
      exact measurableSet_containsFinite S
  have hpi : IsPiSystem C := by
    rintro A ⟨S,rfl⟩ B ⟨T,rfl⟩ _
    exact ⟨S∪T,(containsFinite_inter S T).symm⟩
  apply ext_of_generate_finite C hgen hpi
  · rintro A ⟨S,rfl⟩
    exact h S
  · simp

lemma measurable_intersection : Measurable (fun z : Set E×Set E => z.1∩z.2) :=
  Measurable.of_eval (fun edge => ((measurable_set_mem edge).comp measurable_fst).and
    ((measurable_set_mem edge).comp measurable_snd))

lemma real_containsFinite (p : unitInterval) (S : Finset E) :
    (law (fun _ : E => p)).real (containsFinite S)=(p : ℝ)^S.card := by
  simpa only [containsFinite,Set.ncard_coe_finset] using
    real_law_subset p (S : Set E) S.finite_toSet

theorem law_map_intersection (p r : unitInterval) :
    ((law (fun _ : E => p)).prod (law (fun _ : E => r))).map
      (fun z : Set E×Set E => z.1∩z.2)=law (fun _ : E => p*r) := by
  apply measure_ext_containsFinite
  intro S
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.map_apply measurable_intersection (measurableSet_containsFinite S)]
  have he : (fun z : Set E×Set E => z.1∩z.2) ⁻¹' containsFinite S=
      containsFinite S×ˢcontainsFinite S := by
    ext z
    simp only [Set.mem_preimage,containsFinite,Set.mem_ofPred_eq,Set.mem_prod,
      Set.subset_inter_iff]
  rw [he,Measure.prod_prod,ENNReal.toReal_mul]
  change (law (fun _ : E => p)).real (containsFinite S)*
      (law (fun _ : E => r)).real (containsFinite S)=
      (law (fun _ : E => p*r)).real (containsFinite S)
  rw [real_containsFinite,real_containsFinite,real_containsFinite]
  exact (mul_pow (p : ℝ) (r : ℝ) S.card).symm

lemma law_mono_parameters {p q : unitInterval} (hpq : p≤q)
    (A : Set (Set E)) (hA : MeasurableSet A) (hup : IsUpperSet A) :
    law (fun _ : E => p) A≤law (fun _ : E => q) A := by
  rw [←markLaw_map_atParameter p,←markLaw_map_atParameter q,
    Measure.map_apply (measurable_atParameter p) hA,
    Measure.map_apply (measurable_atParameter q) hA]
  apply measure_mono
  intro u hu
  exact hup (atParameter_mono u hpq) hu

end CriticalPercolation.BernoulliProduct
end
end

end OAI

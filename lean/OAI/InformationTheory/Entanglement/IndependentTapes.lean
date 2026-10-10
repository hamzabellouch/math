import OAI.InformationTheory.Entanglement.KernelSampling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
variable {ι : Type*}
abbrev UniformTapes (ι : Type*) := ι → I
def uniformTapesLaw : Measure (UniformTapes ι) := Measure.infinitePi (fun _ : ι => (volume : Measure I))
instance : IsProbabilityMeasure (uniformTapesLaw (ι := ι)) := by unfold uniformTapesLaw; infer_instance

@[instance_reducible] def tapeInformation (s : Set ι) : MeasurableSpace (UniformTapes ι) :=
  ⨆ i ∈ s, (inferInstance : MeasurableSpace I).comap (fun ω => ω i)
lemma tapeInformation_le (s : Set ι) : tapeInformation s ≤ (inferInstance : MeasurableSpace (UniformTapes ι)) :=
  iSup_le fun i => iSup_le fun _ => (measurable_pi_apply i).comap_le
lemma tapeInformation_mono {s t : Set ι} (h : s ⊆ t) : tapeInformation s ≤ tapeInformation t :=
  iSup_le fun i => iSup_le fun hi => le_iSup_of_le i (le_iSup_of_le (h hi) le_rfl)
lemma tapeInformation_union (s t : Set ι) : tapeInformation (s∪t)=tapeInformation s ⊔ tapeInformation t := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => ?_
    rcases hi with hi|hi
    · exact le_sup_of_le_left (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
  · exact sup_le (tapeInformation_mono Set.subset_union_left) (tapeInformation_mono Set.subset_union_right)
lemma independent_tape_groups {s t : Set ι} (hst : Disjoint s t) :
    Indep (tapeInformation s) (tapeInformation t) uniformTapesLaw := by
  apply indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) _ hst
  exact (iIndepFun_iff_iIndep _ _ _).mp (iIndepFun_infinitePi (X := fun _ (u : I) => u) (by fun_prop))
lemma tape_coordinate_law (i : ι) : uniformTapesLaw.map (fun ω : UniformTapes ι => ω i)=volume :=
  Measure.infinitePi_map_eval _ i
lemma fresh_coordinate_independent {S : Type*} [MeasurableSpace S]
    {s : Set ι} {i : ι} (hi : i∉s) (H : UniformTapes ι → S)
    (hH : Measurable[tapeInformation s] H) :
    IndepFun H (fun ω => ω i) uniformTapesLaw := by
  have h := independent_tape_groups (s := s) (t := {i}) (Set.disjoint_singleton_right.mpr hi)
  apply indep_of_indep_of_le h hH.comap_le
  exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma initial_conditional_independence {A B F : MeasurableSpace Ω}
    (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hF : F ≤ mΩ)
    (hind : Indep B (A ⊔ F) μ) : CondIndep F A B hF μ := by
  apply independence_of_local_marginals hF (sup_le hA hF) le_sup_left le_sup_right hB
  intro b hb
  have hsm : StronglyMeasurable[B] (b.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hb
  exact (condExp_indep_eq hB (sup_le hA hF) hsm hind).trans
    (condExp_indep_eq hB hF hsm (indep_of_indep_of_le_right hind le_sup_right)).symm

theorem initial_uniform_tape_independence [Countable ι]
    {a b c : Set ι} (habc : Disjoint b (a∪c))
    {F : MeasurableSpace (UniformTapes ι)} (hF : F ≤ tapeInformation c) :
    CondIndep F (tapeInformation a) (tapeInformation b) (hF.trans (tapeInformation_le c)) uniformTapesLaw := by
  apply initial_conditional_independence (tapeInformation_le a) (tapeInformation_le b)
    (hF.trans (tapeInformation_le c))
  apply indep_of_indep_of_le_right (independent_tape_groups habc)
  rw [tapeInformation_union]
  exact sup_le_sup_left hF _

end SecretKey

end

end OAI

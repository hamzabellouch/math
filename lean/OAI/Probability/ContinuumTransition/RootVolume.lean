import OAI.Probability.ContinuumTransition.FreeRoots

namespace OAI

universe u_1 u_2

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def rootNeighborhood {ι : Type} [Fintype ι] (a : ι → Space) (r : ℝ) : Set Space :=
  ⋃ i, Metric.closedBall (a i) r

lemma volume_rootNeighborhood {ι : Type} [Fintype ι] (a : ι → Space) (r : ℝ) :
    volume (rootNeighborhood a r) ≤ (Fintype.card ι : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r) := by
  calc
    _ ≤ ∑' i, volume (Metric.closedBall (a i) r) := measure_iUnion_le _
    _ = _ := by simp only [Measure.addHaar_closedBall_center, tsum_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

noncomputable def rootCover {ι : Type} [Fintype ι] (s : Finset ι) (r : ℝ) : Set (ι → Space) :=
  {x | ∀ j : {j : ι // j ∉ s}, ∃ i : {i : ι // i ∈ s}, ‖x j-x i‖ ≤ r}

lemma measurableSet_forall_labels {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Countable ι]
    {P : X → ι → Prop} (hP : ∀ i, MeasurableSet {x | P x i}) : MeasurableSet {x | ∀ i, P x i} := by
  have he : {x | ∀ i, P x i} = ⋂ i, {x | P x i} := by ext x; simp only [mem_ofPred_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.iInter hP

lemma measurableSet_exists_labels {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Countable ι]
    {P : X → ι → Prop} (hP : ∀ i, MeasurableSet {x | P x i}) : MeasurableSet {x | ∃ i, P x i} := by
  have he : {x | ∃ i, P x i} = ⋃ i, {x | P x i} := by ext x; simp only [mem_ofPred_eq, mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion hP

lemma rootCover_volume {ι : Type} [Fintype ι] (s : Finset ι) (r L : ℝ) :
    volume ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r) ≤
      (volume (cube L))^s.card *
        ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) := by
  let I := {i : ι // i ∈ s}
  let J := {i : ι // i ∉ s}
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Space) (fun i => i ∈ s)
  let SA : Set (I → Space) := {a | ∀ i, a i ∈ cube L}
  let T : Set ((I → Space) × (J → Space)) :=
    {z | z.1 ∈ SA ∧ ∀ j, z.2 j ∈ cube L ∩ rootNeighborhood z.1 r}
  have hSA : MeasurableSet SA := measurableSet_forall_labels
    (fun i => (measurableSet_cube L).preimage (measurable_pi_apply i))
  have hT : MeasurableSet T := by
    apply (hSA.preimage measurable_fst).inter
    apply measurableSet_forall_labels
    intro j
    apply ((measurableSet_cube L).preimage ((measurable_pi_apply j).comp measurable_snd)).inter
    change MeasurableSet {z : (I → Space) × (J → Space) | z.2 j ∈ rootNeighborhood z.1 r}
    have he : {z : (I → Space) × (J → Space) | z.2 j ∈ rootNeighborhood z.1 r} =
        {z | ∃ i : I, ‖z.2 j-z.1 i‖ ≤ r} := by
      ext z
      simp only [mem_ofPred_eq, rootNeighborhood, mem_iUnion, Metric.mem_closedBall, dist_eq_norm]
    rw [he]
    apply measurableSet_exists_labels
    intro i
    exact measurableSet_le
      (((measurable_pi_apply j).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).norm measurable_const

  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure Space))
    (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s := Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' T = {x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r := by
    ext x
    change ((∀ i : I, x i ∈ cube L) ∧
      ∀ j : J, x j ∈ cube L ∩ ⋃ i : I, Metric.closedBall (x i) r) ↔
      (∀ i, x i ∈ cube L) ∧ ∀ j : J, ∃ i : I, ‖x j-x i‖ ≤ r
    simp only [mem_inter_iff, mem_iUnion, Metric.mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨ha,hb⟩
      refine ⟨?_,fun j => (hb j).2⟩
      intro i
      by_cases hi : i ∈ s
      · exact ha ⟨i,hi⟩
      · exact (hb ⟨i,hi⟩).1
    · rintro ⟨ha,hb⟩
      exact ⟨fun i => ha i, fun j => ⟨ha j,hb j⟩⟩
  have he := hp.measure_preimage hT.nullMeasurableSet
  rw [hpre] at he
  simp only [← volume_pi] at he
  rw [he, Measure.prod_apply hT]
  let C : ℝ≥0∞ := ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card)
  calc
    _ ≤ ∫⁻ a, SA.indicator (fun _ => C) a := by
      apply lintegral_mono
      intro a
      dsimp only
      by_cases ha : a ∈ SA
      · rw [Set.indicator_of_mem ha]
        have hf : Prod.mk a ⁻¹' T = {b : J → Space | ∀ j, b j ∈ cube L ∩ rootNeighborhood a r} := by
          ext b
          simp only [T, mem_preimage, mem_ofPred_eq, ha, true_and]
        rw [hf, volume_generalConfigurations]
        have hJ : Fintype.card J = Fintype.card ι-s.card := by
          rw [Fintype.card_subtype_compl, Fintype.card_coe]
        rw [hJ]
        apply pow_le_pow_left'
        exact (measure_mono inter_subset_right).trans (by
          simpa only [I, Fintype.card_coe] using volume_rootNeighborhood a r)
      · rw [Set.indicator_of_notMem ha]
        have hf : Prod.mk a ⁻¹' T = ∅ := by ext b; simp [T, ha]
        simp only [hf, measure_empty, le_refl]
    _ = _ := by
      rw [lintegral_indicator_const hSA, volume_generalConfigurations]
      simp only [I, Fintype.card_coe, C, mul_comm]

end ContinuumTemperature
end

end OAI

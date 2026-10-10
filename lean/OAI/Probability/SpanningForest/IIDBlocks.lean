import OAI.Probability.SpanningForest.RandomReindex

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.RandomReindex

theorem indepFun_infinitePi_blocks
    {I J L V : Type*} [MeasurableSpace V]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (a : I → J) (b : L → J)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    IndepFun (fun v : J → V => fun i => v (a i))
      (fun v : J → V => fun l => v (b l))
      (Measure.infinitePi (fun _ : J => ν)) := by
  have hi : iIndep (fun j : J =>
      MeasurableSpace.comap (fun v : J → V => v j) inferInstance)
      (Measure.infinitePi (fun _ : J => ν)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hblocks := indep_iSup_of_disjoint
    (fun j : J => (measurable_iff_comap_le.mp (measurable_pi_apply j))) hi hab
  apply indep_of_indep_of_le hblocks
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro i
    exact le_iSup_of_le (a i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro l
    exact le_iSup_of_le (b l) (le_iSup_of_le ⟨l, rfl⟩ le_rfl)

theorem map_infinitePi_two_blocks
    {I J L V : Type*} [MeasurableSpace V]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (a : I → J) (b : L → J)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    (Measure.infinitePi (fun _ : J => ν)).map
        (fun v : J → V => ((fun i => v (a i)), (fun l => v (b l)))) =
      (Measure.infinitePi (fun _ : I => ν)).prod
        (Measure.infinitePi (fun _ : L => ν)) := by
  rw [(indepFun_infinitePi_blocks ν a b hab).map_prod_eq_prod_map_map
    (Measurable.aemeasurable (Measurable.of_eval (fun i => measurable_pi_apply (a i))))
    (Measurable.aemeasurable (Measurable.of_eval (fun l => measurable_pi_apply (b l)))),
    Measure.map_infinitePi_infinitePi_of_inj ha,
    Measure.map_infinitePi_infinitePi_of_inj hb]

end Problem336.RandomReindex

end

end OAI

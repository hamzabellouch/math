import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem indepFun_prodMk_left_of_joint
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : IndepFun Y Z μ) :
    IndepFun (fun ω => (X ω, Y ω)) Z μ := by
  have hXY : IndepFun X Y μ := hXYZ.comp measurable_id measurable_fst
  have hmapX : IsProbabilityMeasure (μ.map X) := inferInstance
  have hmapY : IsProbabilityMeasure (μ.map Y) := inferInstance
  have hmapZ : IsProbabilityMeasure (μ.map Z) := inferInstance
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable
    hZ.aemeasurable).mpr
  calc
    _ = (μ.map (fun ω => (X ω, Y ω, Z ω))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.map_map (by fun_prop) (hX.prodMk (hY.prodMk hZ))]
      rfl
    _ = ((μ.map X).prod ((μ.map Y).prod (μ.map Z))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable,
        hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]
    _ = ((μ.map X).prod (μ.map Y)).prod (μ.map Z) :=
      (measurePreserving_prodAssoc (μ.map X) (μ.map Y) (μ.map Z)).symm.map_eq
    _ = _ := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

theorem condIndepFun_prodMk_left_of_joint
    {Ω S A B C : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : Ω → S} {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hR : Measurable R) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le Y Z μ) :
    CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      (fun ω => (X ω, Y ω)) Z μ := by
  apply (condIndepFun_iff_indepFun_cond_fibers hR (hX.prodMk hY) hZ).mpr
  intro s hs
  let : IsProbabilityMeasure μ[|R ⁻¹' {s}] := cond_isProbabilityMeasure hs
  exact indepFun_prodMk_left_of_joint hX hY hZ
    (indepFun_cond_fiber_of_condIndepFun hR hX (hY.prodMk hZ) hXYZ s)
    (indepFun_cond_fiber_of_condIndepFun hR hY hZ hYZ s)

theorem condIndepFun_coordinate_others
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ} {F : ∀ i, Ω → B i}
    (hF : ∀ i, @Measurable Ω (B i) mΩ (mB i) (F i)) (hI : iCondIndepFun m hm F μ) (c : ι) :
    CondIndepFun m hm (F c) (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω) μ := by
  let : MeasurableSpace Ω := mΩ
  have hle : ∀ i : ι, MeasurableSpace.comap (F i) (mB i) ≤ mΩ :=
    fun i => (hF i).comap_le
  have hd : Disjoint ({c} : Set ι) {i | i ≠ c} := by simp
  have h := condIndep_iSup_of_disjoint hle hI hd
  change CondIndep m
    (MeasurableSpace.comap (F c) (mB c))
    (MeasurableSpace.comap (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω)
      inferInstance) hm μ
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

end Problem367

end

end OAI

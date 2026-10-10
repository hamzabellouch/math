import OAI.Analysis.CircleDomains.Topology.CrosscutPathSides
import OAI.Analysis.CircleDomains.Probability.RayFamilyMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Both sides have analytic path descriptions, so their membership sets
are Borel by Suslin's theorem. This avoids a measurable Schoenflies choice. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem isClosed_pathPairMeet :
    IsClosed {p : C(PathTime, ℂ) × C(PathTime, ℂ) | ¬ Disjoint (range p.1) (range p.2)} := by
  let E : Set ((C(PathTime, ℂ) × C(PathTime, ℂ)) × (PathTime × PathTime)) :=
    {p | p.1.1 p.2.1 = p.1.2 p.2.2}
  have hE : IsClosed E := isClosed_eq
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.fst))
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd))
  have he : Prod.fst '' E = {p : C(PathTime, ℂ) × C(PathTime, ℂ) |
      ¬ Disjoint (range p.1) (range p.2)} := by
    ext p
    constructor
    · rintro ⟨⟨_, s, t⟩, h, rfl⟩ hd
      exact Set.disjoint_left.mp hd (mem_range_self s) (h ▸ mem_range_self t)
    · intro h
      obtain ⟨z, hz, hw⟩ := Set.not_disjoint_iff.mp h
      obtain ⟨s, hs⟩ := hz
      obtain ⟨t, ht⟩ := hw
      exact ⟨(p, s, t), hs.trans ht.symm, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace E hE

 theorem analyticSet_diskAvoidingPath {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (p : X → C(PathTime, ℂ)) (hp : Measurable p)
    (z w : X → ℂ) (hz : Measurable z) (hw : Measurable w) :
    AnalyticSet {x | DiskAvoidingPath (p x) (z x) (w x)} := by
  let E : Set (X × C(PathTime, ℂ)) := {q |
    q.2 0 = z q.1 ∧ q.2 1 = w q.1 ∧
      (∀ t, q.2 t ∈ Metric.closedBall 0 1) ∧ Disjoint (range (p q.1)) (range q.2)}
  have hball : IsClosed {δ : C(PathTime, ℂ) | ∀ t, δ t ∈ Metric.closedBall 0 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => Metric.isClosed_closedBall.preimage (continuous_eval_const t)
  have hE : MeasurableSet E := by
    have hmiss : MeasurableSet {q : X × C(PathTime, ℂ) |
        Disjoint (range (p q.1)) (range q.2)} := by
      convert (isClosed_pathPairMeet.measurableSet.compl.preimage
        ((hp.comp measurable_fst).prodMk measurable_snd)) using 1
      ext q
      change Disjoint (range (p q.1)) (range q.2) ↔ ¬¬ Disjoint (range (p q.1)) (range q.2)
      exact not_not.symm
    exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      (hz.comp measurable_fst)).inter
      ((measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        (hw.comp measurable_fst)).inter
        ((hball.measurableSet.preimage measurable_snd).inter hmiss))
  have he : Prod.fst '' E = {x | DiskAvoidingPath (p x) (z x) (w x)} := by
    ext x
    constructor
    · rintro ⟨⟨x, δ⟩, h, rfl⟩
      refine ⟨δ, h.1, h.2.1, fun t => ⟨h.2.2.1 t, ?_⟩⟩
      intro ht
      exact Set.disjoint_left.mp h.2.2.2 ht (mem_range_self t)
    · rintro ⟨δ, h0, h1, hδ⟩
      refine ⟨(x, δ), ⟨h0, h1, fun t => (hδ t).1, ?_⟩, rfl⟩
      apply Set.disjoint_left.mpr
      rintro u hu ⟨t, rfl⟩
      exact (hδ t).2 hu
  rw [← he]
  exact hE.analyticSet.image_of_continuous continuous_fst

 theorem measurableSet_rayRightFamily {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hsep : UnitDiskCrosscutSeparation)
    (R : X → HalfPlaneRay) (H : X → ℂ ≃ₜ ℂ) (hH : ∀ x, (R x).IsJordan (H x))
    (hp : Measurable (fun x => (R x).crosscut.toContinuousMap))
    (ha : Measurable (fun x => ((R x).curve ⟨0, bot_lt_top⟩).re))
    (z : X → ℂ) (hz : Measurable z) (hzd : ∀ x, z x ∈ Metric.closedBall 0 1) :
    MeasurableSet {x | z x ∉ closure (jordanInterior (H x))} := by
  have hM : Measurable halfPlaneDisk := by unfold halfPlaneDisk; fun_prop
  have hplus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.add_const 1))
  have hminus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.sub_const 1))
  have hright : AnalyticSet {x | z x ∉ closure (jordanInterior (H x))} := by
    have he : {x | z x ∉ closure (jordanInterior (H x))} =
        {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
          (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ))} := by
      ext x
      exact (R x).right_iff_avoidingPath hsep (hH x) (hzd x)
    rw [he]
    exact analyticSet_diskAvoidingPath _ hp z _ hz hplus
  apply hright.measurableSet_of_compl
  have hhit : MeasurableSet {x | z x ∈ range (R x).crosscut} :=
    isClosed_pathHitSet.measurableSet.preimage (hp.prodMk hz)
  have hleft := analyticSet_diskAvoidingPath _ hp z _ hz hminus
  have he : {x | z x ∉ closure (jordanInterior (H x))}ᶜ =
      {x | z x ∈ range (R x).crosscut} ∪
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))} := by
    ext x
    simpa only [mem_compl_iff, mem_ofPred_eq, not_not, mem_union] using
      (R x).left_iff_hit_or_avoidingPath hsep (hH x) (hzd x)
  rw [he]
  have hu := AnalyticSet.iUnion (s := fun b : Bool => if b then
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))}
      else {x | z x ∈ range (R x).crosscut})
    (fun b => by cases b; exact hhit.analyticSet; exact hleft)
  convert hu using 1
  ext x
  constructor
  · rintro (h | h)
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  · intro h
    obtain ⟨b, hb⟩ := mem_iUnion.mp h
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

end CircleDomainRigidity

end

end OAI

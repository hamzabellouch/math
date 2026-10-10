import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCharts
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! A measurable choice of representatives for the actual principal
quotient, obtained from a countable disjoint refinement of covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

instance cubicThetaPoint_measurableSpace : MeasurableSpace CubicThetaPoint := borel _
instance cubicThetaPoint_borelSpace : BorelSpace CubicThetaPoint := ⟨rfl⟩
instance cubicThetaQuotient_measurableSpace : MeasurableSpace CubicThetaQuotient := borel _
instance cubicThetaQuotient_borelSpace : BorelSpace CubicThetaQuotient := ⟨rfl⟩

lemma cubicThetaQuotientChart_source_eq (c : CubicThetaQuotient) :
    (cubicThetaQuotientChart c).source=
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)).target := by
  ext q
  change (q∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).target ∧
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)).symm q∈cubicThetaPointInclusion.source)↔_
  rw [cubicThetaPointInclusion_source]
  simp only [mem_univ,and_true]

lemma cubicTheta_countable_chart_cover :
    ∃ c : ℕ → CubicThetaQuotient, ∀ q, ∃ n, q∈(cubicThetaQuotientChart (c n)).source := by
  obtain ⟨S,hSc,hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun c : CubicThetaQuotient => (cubicThetaQuotientChart c).source)
    (fun c => (cubicThetaQuotientChart c).open_source) (by
      intro q _
      exact mem_iUnion.mpr ⟨q,cubicThetaQuotientChart_source q⟩)
  have hSne : S.Nonempty := by
    let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
    obtain ⟨c,hc,_⟩ := mem_iUnion₂.mp (hS (mem_univ (cubicThetaQuotientMap p)))
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hSc.exists_eq_range hSne
  refine ⟨c,fun q => ?_⟩
  obtain ⟨d,hd,hqd⟩ := mem_iUnion₂.mp (hS (mem_univ q))
  rw [hc] at hd
  obtain ⟨n,rfl⟩ := hd
  exact ⟨n,hqd⟩

def cubicThetaAtlasCenter : ℕ → CubicThetaQuotient :=
  Classical.choose cubicTheta_countable_chart_cover

def cubicThetaAtlasOpen (n : ℕ) : Set CubicThetaQuotient :=
  (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).source

def cubicThetaAtlasPiece (n : ℕ) : Set CubicThetaQuotient :=
  disjointed cubicThetaAtlasOpen n

lemma cubicThetaAtlasPiece_measurable (n : ℕ) : MeasurableSet (cubicThetaAtlasPiece n) :=
  MeasurableSet.disjointed (fun n => (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).open_source.measurableSet) n

lemma cubicThetaAtlasPiece_cover : ⋃ n, cubicThetaAtlasPiece n=univ := by
  change (⋃ n, disjointed cubicThetaAtlasOpen n)=univ
  rw [iUnion_disjointed]
  apply eq_univ_of_forall
  intro q
  exact mem_iUnion.mpr (Classical.choose_spec cubicTheta_countable_chart_cover q)

def cubicThetaAtlasLocalLift (n : ℕ) : CubicThetaQuotient → CubicThetaPoint :=
  (cubicThetaAtlasOpen n).piecewise
    (cubicThetaCoveringChart (cubicThetaQuotientLift (cubicThetaAtlasCenter n))).symm
    (fun _ => cubicThetaQuotientLift (cubicThetaAtlasCenter n))

lemma cubicThetaAtlasLocalLift_measurable (n : ℕ) : Measurable (cubicThetaAtlasLocalLift n) := by
  apply ContinuousOn.measurable_piecewise
  · change ContinuousOn _ (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).source
    rw [cubicThetaQuotientChart_source_eq]
    exact (cubicThetaCoveringChart _).symm.continuousOn
  · exact continuous_const.continuousOn
  · exact (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).open_source.measurableSet

lemma cubicThetaAtlasLocalLift_rightInverse (n : ℕ) {q : CubicThetaQuotient}
    (hq : q∈cubicThetaAtlasPiece n) :
    cubicThetaQuotientMap (cubicThetaAtlasLocalLift n q)=q := by
  have hu := disjointed_subset cubicThetaAtlasOpen n hq
  rw [cubicThetaAtlasLocalLift,piecewise_eq_of_mem _ _ _ hu]
  rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift (cubicThetaAtlasCenter n))]
  apply (cubicThetaCoveringChart _).right_inv
  exact (cubicThetaQuotientChart_source_eq _ ▸ hu)

lemma cubicTheta_measurable_section_exists :
    ∃ s : CubicThetaQuotient → CubicThetaPoint,
      Measurable s ∧ Function.RightInverse s cubicThetaQuotientMap := by
  obtain ⟨s,hs,hse⟩ := exists_measurable_piecewise cubicThetaAtlasPiece
    cubicThetaAtlasPiece_measurable cubicThetaAtlasLocalLift cubicThetaAtlasLocalLift_measurable (by
      intro i j hij q hq
      exact False.elim (Set.disjoint_left.mp (disjoint_disjointed cubicThetaAtlasOpen hij) hq.1 hq.2))
  refine ⟨s,hs,fun q => ?_⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp (cubicThetaAtlasPiece_cover.symm ▸ mem_univ q)
  rw [hse n hn]
  exact cubicThetaAtlasLocalLift_rightInverse n hn

end CubicFirstMoment

end

end OAI

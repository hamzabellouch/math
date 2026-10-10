import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapRegularLocus
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCoordinateStrip

namespace OAI

/-! A thin actual source rectangle has no singularities except the two
specified endpoint crosscaps. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.regular_neighborhood (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ U : Set Base, IsOpen U ∧ U ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U) ∧
      ∀ x ∈ U, Function.Injective (fderiv ℝ S.model x) ↔
        x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] := by
  let R := {y | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y)}
  let O := A.left.source.source ∪ A.right.source.source ∪ R
  have hO : IsOpen O := (A.left.source.open_source.union A.right.source.open_source).union
    (surface_regular_locus_open hf)
  let U := S.domain ∩ (S.chart.target ∩ S.chart.symm ⁻¹' O)
  have hU : IsOpen U := S.domain_open.inter (S.chart.symm.isOpen_inter_preimage hO)
  have haxisU : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    have hs := S.axis t ht
    have hx : (![0,t] : Base) ∈ S.domain := by
      apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
      constructor <;> linarith [S.width_pos,ht.1,ht.2]
    refine ⟨hx,S.domain_target hx,?_⟩
    change S.chart.symm (![0,t] : Base) ∈ O
    rw [← hs.2,S.chart.left_inv hs.1]
    by_cases hts : t = A.arc.start
    · rw [hts,A.source]
      exact Or.inl (Or.inl A.left.source_mem)
    · by_cases htf : t = A.arc.finish
      · rw [htf,A.target]
        exact Or.inl (Or.inr A.right.source_mem)
      · exact Or.inr (A.regular t ⟨lt_of_le_of_ne ht.1 (Ne.symm hts),lt_of_le_of_ne ht.2 htf⟩)
  have hpsource : p ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.source).mp
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hqsource : q ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.target).mp
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hpchart : S.chart p = ![0,A.arc.start] :=
    (congrArg S.chart A.source).symm.trans
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hqchart : S.chart q = ![0,A.arc.finish] :=
    (congrArg S.chart A.target).symm.trans
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hprecover : S.chart.symm (![0,A.arc.start] : Base) = p :=
    (congrArg S.chart.symm hpchart).symm.trans (S.chart.left_inv hpsource)
  have hqrecover : S.chart.symm (![0,A.arc.finish] : Base) = q :=
    (congrArg S.chart.symm hqchart).symm.trans (S.chart.left_inv hqsource)
  refine ⟨U,hU,inter_subset_left,haxisU,?_⟩
  intro x hx
  have hbridge := coordinate_representative_immersion_iff S.chart S.chart_smooth S.inverse_smooth hf
    S.domain_open S.domain_target S.model_eq hx.1
  rw [hbridge]
  constructor
  · intro h
    constructor
    · intro he
      rw [he,hprecover] at h
      exact ((A.left.regular_iff hf A.left.source_mem).mp h) rfl
    · intro he
      rw [he,hqrecover] at h
      exact ((A.right.regular_iff hf A.right.source_mem).mp h) rfl
  · rintro ⟨hxp,hxq⟩
    have hyp : S.chart.symm x ≠ p := by
      intro h
      apply hxp
      calc
        x = S.chart (S.chart.symm x) := (S.chart.right_inv hx.2.1).symm
        _ = S.chart p := congrArg S.chart h
        _ = ![0,A.arc.start] := hpchart
    have hyq : S.chart.symm x ≠ q := by
      intro h
      apply hxq
      calc
        x = S.chart (S.chart.symm x) := (S.chart.right_inv hx.2.1).symm
        _ = S.chart q := congrArg S.chart h
        _ = ![0,A.arc.finish] := hqchart
    rcases hx.2.2 with (hleft | hright) | hreg
    · exact (A.left.regular_iff hf hleft).mpr hyp
    · exact (A.right.regular_iff hf hright).mpr hyq
    · exact hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

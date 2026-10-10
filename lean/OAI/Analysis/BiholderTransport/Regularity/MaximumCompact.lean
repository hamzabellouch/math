import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.GraphCoordinates
import OAI.Analysis.BiholderTransport.Regularity.MaximumFamily

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def MaximumFamily.comp {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    MaximumFamily (n := n) v α D bminus bplus Bc Bo where
  t := F.t ∘ σ
  b := F.b ∘ σ
  z := F.z ∘ σ
  prefixTime k := F.prefixTime (σ k)
  parameter k := F.parameter (σ k)
  time := F.time.comp hσ
  positive k := F.positive (σ k)
  maximum k := F.maximum (σ k)
  row k := F.row (σ k)

lemma MaximumFamily.compact_subseq {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) :
    ∃ σ:ℕ → ℕ,StrictMono σ ∧ ∃ β∈Icc bminus bplus,
      ∃ Q:TangentBundle 𝓘(ℝ,Model n) M,Q.2∈minimizingVectors Q.1 ∧
        Tendsto (F.b ∘ σ) atTop (𝓝 β) ∧
        Tendsto (fun k=>(F.row (σ k)).q.1) atTop (𝓝 Q) := by
  let : FirstCountableTopology (ModelProd (Model n) (Model n)) :=
    inferInstanceAs (FirstCountableTopology (Model n×Model n))
  let : FirstCountableTopology (TangentBundle 𝓘(ℝ,Model n) M) := by
    constructor
    intro x
    let e := chartAt (ModelProd (Model n) (Model n)) x
    have he : map e.symm (𝓝 (e x))=𝓝 x := e.symm_map_nhds_eq (mem_chart_source _ _)
    rw [←he]
    infer_instance
  have hc := isCompact_Icc (a := bminus) (b := bplus) |>.prod
    (isCompact_total_minimizingVectors (n := n) (M := M))
  obtain ⟨q,hq,σ,hσ,hlim⟩ := hc.isSeqCompact (fun k=>
    show (F.b k,(F.row k).q.1)∈Icc bminus bplus×ˢ
      {Q:TangentBundle 𝓘(ℝ,Model n) M | Q.2∈minimizingVectors Q.1} from
        ⟨Ioo_subset_Icc_self (F.parameter k),(F.row k).minimizing⟩)
  exact ⟨σ,hσ,q.1,hq.1,q.2,hq.2,hlim.fst_nhds,hlim.snd_nhds⟩

lemma MaximumFamily.limit_coordinates {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) :
    Tendsto (fun k=>graphBaseCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) Q.1 Q.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop (𝓝 (show Model n from Q.2)) ∧
    Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) ∧
    Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) atTop
      (𝓝 (riemannianExp Q.1 Q.2)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨Q.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : Q∈χ.source := (tangent_chart_source_iff _ _).mpr (mem_extChartAt_source Q.1)
  have HC := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hQ
  have hvel : Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (graphVelocityCoordinate Q.1 Q)) := HC.snd_nhds
  rw [graph_coordinates_at_center] at hvel
  have HE := contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have HP := (contMDiff_riemannianExp.continuous.comp contMDiff_tangentScale.continuous).tendsto (1,Q)
    |>.comp (F.time.prodMk_nhds hQ)
  have HZ : Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) := by
    change Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.t k • (F.row k).q.1.2)) atTop
      (𝓝 (riemannianExp Q.1 ((1:ℝ) • Q.2))) at HP
    simp only [one_smul] at HP
    exact HP.congr (fun k=>(F.row k).projection)
  exact ⟨HC.fst_nhds,hvel,HZ,HE⟩
end WeakMTWTransport

end

end OAI

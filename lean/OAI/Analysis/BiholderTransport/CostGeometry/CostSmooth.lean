import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TotalInjectivity

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_contMDiffAt_of_injectivityDomain (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (z.1,riemannianExp z.1 z.2) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let c := extChartAt 𝓘(ℝ,Model n) z.1
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let y : M×M := (z.1,riemannianExp z.1 z.2)
  let J : M×M → Model n × Model n := fun q => (c q.1,d q.2)
  obtain ⟨e,he,hze,_,hend,_,hei⟩ := exists_joint_exp_inverse z hz
  have hχz := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hJy : J y = e (χ z) := by
    rw [he]
    change (c z.1,d (riemannianExp z.1 z.2)) =
      ((χ z).1,d (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2))
    rw [hχinv]
    rfl
  have hyT : J y ∈ e.target := hJy ▸ e.map_source hze
  have hiy : e.symm (J y)=χ z := by rw [hJy,e.left_inv hze]
  have hJ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n × Model n) ∞ J y := by
    have hc₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ c y.1 := contMDiffAt_extChartAt
    have hd₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y.2 := contMDiffAt_extChartAt
    exact (hc₀.comp y contMDiffAt_fst).prodMk_space (hd₀.comp y contMDiffAt_snd)
  have hi := (hei.contDiffAt (e.open_target.mem_nhds hyT)).contMDiffAt.comp y hJ
  have hc : ContMDiffAt 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm
      (e.symm (J y)) :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt ((isOpen_extChartAt_target z).mem_nhds (hiy ▸ hχz))
  let P : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => χ.symm (e.symm (J q))
  have hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P y :=
    hc.comp y hi
  have hPy : P y = z := by dsimp [P]; rw [hiy,hχinv]
  have hmin : ∀ᶠ q in 𝓝 y, (P q).2 ∈ minimizingVectors (P q).1 := by
    have hC : {r : TangentBundle 𝓘(ℝ,Model n) M | r.2 ∈ minimizingVectors r.1} ∈ 𝓝 (P y) := by
      rw [hPy]
      exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors z hz)
    exact hP.continuousAt.preimage_mem_nhds hC
  have hJnear : ∀ᶠ q in 𝓝 y, J q ∈ e.target := hJ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hyT)
  have hcharts : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source ∧ q.2 ∈ d.source := by
    have hcnear : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source :=
      (continuous_fst : Continuous (fun q : M×M => q.1)).continuousAt.preimage_mem_nhds
        (show c.source ∈ 𝓝 y.1 from extChartAt_source_mem_nhds z.1)
    have hdnear : ∀ᶠ q : M×M in 𝓝 y, q.2 ∈ d.source :=
      (continuous_snd : Continuous (fun q : M×M => q.2)).continuousAt.preimage_mem_nhds
        (show d.source ∈ 𝓝 y.2 from extChartAt_source_mem_nhds (riemannianExp z.1 z.2))
    exact hcnear.and hdnear
  apply ((contMDiff_tangent_energy (P y)).comp y hP).congr_of_eventuallyEq
  filter_upwards [hmin,hJnear,hcharts] with q hqmin hqJ hqc
  have his := e.map_target hqJ
  have hmap := e.right_inv hqJ
  rw [he] at hmap
  have hfirst : (P q).1=q.1 := by
    change (χ.symm (e.symm (J q))).1=q.1
    rw [tangent_chart_symm_base]
    have hf := congrArg Prod.fst hmap
    change (e.symm (J q)).1=c q.1 at hf
    rw [hf,c.left_inv hqc.1]
  have hlast : riemannianExp (P q).1 (P q).2=q.2 := by
    apply d.injOn (hend _ his) hqc.2
    exact congrArg Prod.snd hmap
  change dist q.1 q.2^2/2 = ‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  calc
    dist q.1 q.2^2/2 = dist (P q).1 (riemannianExp (P q).1 (P q).2)^2/2 := by rw [hlast,hfirst]
    _ = _ := by rw [hqmin]

end WeakMTWTransport

end

end OAI

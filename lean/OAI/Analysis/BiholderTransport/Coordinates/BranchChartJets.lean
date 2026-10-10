import Mathlib
import OAI.Analysis.BiholderTransport.Model
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchChartJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma branch_chart_jet_continuous {G : M×M → ℝ} {a y : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      G ((extChartAt 𝓘(ℝ,Model n) a).symm z,y)) :
    ContinuousAt (fun q : Model n×M => fderiv ℝ (fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) q.1) (z,y) ∧
    ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)))) q.1) (z,y) ∧
    ∀ᶠ q : Model n×M in 𝓝 (z,y), ContDiffAt ℝ 2 ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2))) q.1 := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let d := extChartAt 𝓘(ℝ,Model n) y
  let F : Model n → Model n → ℝ := fun b z => G (χ.symm z,d.symm b)
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => χ.symm q.2) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target a hz).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hz)).comp (d y,z) contDiffAt_snd.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => d.symm q.1) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target y
      (d.map_source (mem_extChartAt_source y))).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))).comp
      (d y,z) contDiffAt_fst.contMDiffAt
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (d y,z) := by
    have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      G (χ.symm z,d.symm (d y)) := by simpa only [hdy] using hc
    exact (hc'.comp (d y,z) (hA.prodMk hB)).contDiffAt
  have hchart : ContinuousAt d y := continuousAt_extChartAt y
  have hq : ContinuousAt (fun q : Model n×M => (d q.2,q.1)) (z,y) :=
    (hchart.comp (x := (z,y)) (f := fun q : Model n×M => q.2) continuousAt_snd).prodMk continuousAt_fst
  have hnear : ∀ᶠ q : Model n×M in 𝓝 (z,y), q.2∈d.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have heq : ∀ᶠ q : Model n×M in 𝓝 (z,y), F (d q.2)=(fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) := by
    filter_upwards [hnear] with q hq
    funext w
    dsimp [F,χ]
    rw [d.left_inv hq]
  refine ⟨?_,?_,?_⟩
  · have H := (ContDiffAt.partial_snd_fderiv hF).continuousAt.comp
      (x := (z,y)) (f := fun q : Model n×M => (d q.2,q.1)) hq
    apply H.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    change fderiv ℝ (fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) q.1 =
      fderiv ℝ (F (d q.2)) q.1
    rw [hq]
  · have H := (ContDiffAt.partial_snd_fderiv_two hF).continuousAt.comp
      (x := (z,y)) (f := fun q : Model n×M => (d q.2,q.1)) hq
    apply H.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    change fderiv ℝ (fderiv ℝ ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)))) q.1 =
      fderiv ℝ (fderiv ℝ (F (d q.2))) q.1
    rw [hq]
  · have H := (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)
    filter_upwards [hq.tendsto.eventually H,heq] with q hq he
    have H' := hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
    change ContDiffAt ℝ 2 (F (d q.2)) q.1 at H'
    rw [he] at H'
    exact H'

end BranchChartJets
end WeakMTWTransport

end

end

end

end OAI

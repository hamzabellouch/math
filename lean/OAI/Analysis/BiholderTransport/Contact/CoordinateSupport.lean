import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CostSmooth
import OAI.Analysis.BiholderTransport.Regularity.ContDiffParametricQuadratic

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
section CoordinateSupport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma smooth_coordinate_half_cost_quadratic {A : Type*} [TopologicalSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → M} (hψ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Model n) ∞ ψ 0)
    {Y : A → M} {a : A} (hY : ContinuousAt Y a) {x : M} (hx : ψ 0=x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hya : Y a=riemannianExp x ((1/2:ℝ) • p)) :
    ∃ δ>0, ∃ K>0, ∀ᶠ b in 𝓝 a,
      ∀ z∈Metric.ball (0:E) δ,
        ∃ l : E →L[ℝ] ℝ,
          ∀ w∈Metric.ball (0:E) δ,
            2*(cost (ψ w) (Y b)-cost (ψ z) (Y b))-
              l (w-z) ≤ K*‖w-z‖^2 := by
  let y := riemannianExp x ((1/2:ℝ) • p)
  let d := extChartAt 𝓘(ℝ,Model n) y
  have hyS : y∈d.source := mem_extChartAt_source y
  have hyT : d y∈d.target := d.map_source hyS
  have hdy : d.symm (d y)=y := d.left_inv hyS
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let F := fun q : E×Model n => (2:ℝ)*cost (ψ q.1) (d.symm q.2)
  have hA : ContMDiffAt 𝓘(ℝ,E×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : E×Model n => ψ q.1) (0,d y) :=
    hψ.comp (0,d y) contDiffAt_fst.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,E×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : E×Model n => d.symm q.2) (0,d y) :=
    ((contMDiffWithinAt_extChartAt_symm_target y hyT).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hyT)).comp (0,d y) contDiffAt_snd.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨x,(1/2:ℝ) • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hID
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (ψ (0:E),d.symm (d y)) := by
    simpa only [hx,hdy] using hC
  have hF0 := hC'.comp (0,d y) (hA.prodMk hB)
  have hF : ContDiffAt ℝ ∞ F (0,d y) := by
    simpa only [Function.comp_def] using contDiffAt_const.mul hF0.contDiffAt
  obtain ⟨δ,hδ,K,hK,H⟩ := contDiffAt_parametric_quadratic_upper hF
  have hc : ContinuousAt (fun b => d (Y b)) a :=
    (show ContinuousAt d (Y a) by rw [hya]; exact continuousAt_extChartAt y).comp hY
  have hdY : ∀ᶠ b in 𝓝 a, d (Y b)∈Metric.ball (d y) δ := by
    apply hc.preimage_mem_nhds
    apply Metric.isOpen_ball.mem_nhds
    simpa only [hya,Metric.mem_ball,y,dist_self] using hδ
  have hsrc : ∀ᶠ b in 𝓝 a, Y b∈d.source :=
    hY.preimage_mem_nhds ((isOpen_extChartAt_source y).mem_nhds (hya.symm ▸ hyS))
  refine ⟨δ,hδ,K,hK,?_⟩
  filter_upwards [hdY,hsrc] with b hb hbs
  intro z hz
  refine ⟨(fderiv ℝ F (z,d (Y b))).comp (ContinuousLinearMap.inl ℝ E (Model n)),?_⟩
  intro w hw
  have HH := H z hz w hw (d (Y b)) hb
  dsimp only [F] at HH
  rw [d.left_inv hbs] at HH
  change 2*(cost (ψ w) (Y b)-cost (ψ z) (Y b))-
    (fderiv ℝ F (z,d (Y b))) (w-z,0) ≤ K*‖w-z‖^2
  change 2*cost (ψ w) (Y b)-2*cost (ψ z) (Y b)-
    (fderiv ℝ F (z,d (Y b))) (w-z,0) ≤ K*‖w-z‖^2 at HH
  simpa only [mul_sub] using HH

end CoordinateSupport
end WeakMTWTransport

end

end

end

end OAI

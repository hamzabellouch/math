import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters
import OAI.Analysis.BiholderTransport.Coordinates.LocalOuterLog

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterCoordinate
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_outer_coordinate_jet_bound (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
    {p:Model n} (hmin:p∈minimizingVectors a)
    (hnc:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp a p) (riemannianExp a v)) p))
    {l:ℝ} (hl:1 < l) :
    ∃U:Set ((Model n×Model n)×ℝ),U∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),l) ∧ ∃C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (movingNormal a q.1)) →
      HasDerivAt φ q.2 (uv.2 (movingNormal a q.1)) →
      iteratedDeriv 2 φ (uv.2 (movingNormal a q.1)) ≤ 0 →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
        ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨a,p⟩
  have H:=hmtw.exists_local_outer_log_jet_bound hlam hcap z hmin hnc hl
  dsimp only at H
  have hz:extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z z=
      (extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)) := tangent_chart_at_self_base z p
  rw [hz] at H
  obtain ⟨U,hU,C,hC,HC⟩:=H
  let V:=U∩(fun q:(Model n×Model n)×ℝ=>q.1.1) ⁻¹' (extChartAt 𝓘(ℝ,Model n) a).target
  have hV:V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),l) :=
    inter_mem hU ((continuous_fst.comp continuous_fst).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target a)))
  refine ⟨V,hV,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc B hB hjet d
  have hqt:q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).target := hq.2
  apply HC q hq.1 x0 uv huv φ hmono
  · exact hφ
  · exact hd
  · exact hconc
  · exact hB
  · convert hjet using 1
    funext δ
    have he:=tangent_chart_symm_trivialization (q := (q.1.1,q.1.2+δ)) hqt
    change (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z).symm (q.1.1,q.1.2+δ)=_ at he
    rw [he]
    simp only [movingNormal_eq hqt]
end OuterCoordinate
end WeakMTWTransport

end
end

end OAI

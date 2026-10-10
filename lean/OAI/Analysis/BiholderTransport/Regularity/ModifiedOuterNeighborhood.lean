import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ScalarSecond
import OAI.Analysis.BiholderTransport.Regularity.ActiveOuter
import OAI.Analysis.BiholderTransport.Coordinates.OuterCoordinate
import OAI.Analysis.BiholderTransport.Calculus.ScalarJetNeighborhood

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ModifiedOuterNeighborhood
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_neighborhood (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {Φ:ℝ×ℝ → ℝ} (hΦ:ContDiff ℝ ∞ Φ) {β:ℝ} (hmono:StrictMono (fun s=>Φ (β,s)))
    {a:M} {p:Model n}
    (ha:p∈activeLogs (fun y=>Φ (β,uv.2 y)) a)
    (hslope:1 < deriv (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)))
    (hcurve:iteratedDeriv 2 (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)) < 0) :
    ∃V:Set ((Model n×Model n)×ℝ),V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β) ∧
      ∃C≥0,∀q∈V,StrictMono (fun s=>Φ (q.2,s)) →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>Φ (q.2,uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
        ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  have hφ:=scalar_family_contDiff hΦ β
  have hφ2:ContDiff ℝ 2 (fun s=>Φ (β,s)):=hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnc:=hmtw.active_outer_nonconjugate hlam hcap huv hφ.continuous hmono
    (z := (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)) ha hφ2.contDiffAt (scalar_family_derivable hΦ (β,uv.2 (riemannianExp a p))) hslope hcurve.le
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.exists_outer_coordinate_jet_bound hlam hcap ha.1 hnc hslope
  let q0:(Model n×Model n)×ℝ:=((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β)
  have he:movingNormal a q0.1=riemannianExp a p := by
    change movingNormal a (extChartAt 𝓘(ℝ,Model n) a a,p)=_
    rw [movingNormal_eq (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)]
    change riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a))
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a) p)=_
    rw [chartFiberInverse_at_center]
    congr 1
    exact (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  have hf:ContinuousAt (fun q:Model n×Model n=>uv.2 (movingNormal a q)) q0.1 :=
    uv.2.continuous.continuousAt.comp ((movingNormal_contMDiffAt
      (q := q0.1) (mem_extChartAt_target a)).continuousAt)
  obtain ⟨V,hV,HV⟩:=scalar_jet_neighborhood hf (continuous_scalar_family_deriv hΦ) (continuous_scalar_family_second hΦ)
    (by simpa only [he,q0] using hU) (by simpa only [he,q0] using hcurve)
  refine ⟨V,hV,C,hC,?_⟩
  intro q hq hm B hB hjet d
  exact HC _ (HV q hq).1 x0 uv huv (fun s=>Φ (q.2,s)) hm
    (((scalar_family_contDiff hΦ q.2).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt)
    (scalar_family_derivable hΦ (q.2,uv.2 (movingNormal a q.1))) (HV q hq).2.le B hB hjet d

end ModifiedOuterNeighborhood
end WeakMTWTransport

end
end

end OAI

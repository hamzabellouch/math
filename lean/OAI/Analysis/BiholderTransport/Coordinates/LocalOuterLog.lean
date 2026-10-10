import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.EndpointLowerJet
import OAI.Analysis.BiholderTransport.Calculus.FiberJet
import OAI.Analysis.BiholderTransport.CostGeometry.BranchJetSecond

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalOuterLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_outer_log_jet_bound (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap)
    (z:TangentBundle 𝓘(ℝ,Model n) M) (hmin:z.2∈minimizingVectors z.1)
    (hnc:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2))
    {l:ℝ} (hl:1 < l) :
    let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
    ∃U:Set ((Model n×Model n)×ℝ),U∈𝓝 (χ z,l) ∧ ∃C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      let r:=χ.symm q.1
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (riemannianExp r.1 r.2)) →
      HasDerivAt φ q.2 (uv.2 (riemannianExp r.1 r.2)) →
      iteratedDeriv 2 φ (uv.2 (riemannianExp r.1 r.2)) ≤ 0 →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>
        let s:=χ.symm (q.1.1,q.1.2+d)
        φ (uv.2 (riemannianExp s.1 s.2))+‖s.2‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  dsimp only
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d:=extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  obtain ⟨e,he,hze,heχ,hes,hfe,hge⟩:=exists_joint_exp_inverse_of_nonconjugate z hnc
  have hefirst:∀q,(e q).1=q.1 := by intro q; rw [he]
  obtain ⟨W,hW,hWe,K,hK,HK⟩:=exists_uniform_fiber_jet_transfer e hefirst hfe hge hze
  obtain ⟨G,hG,hact,hagree⟩:=exists_reverse_branch_with_forward_action z hnc
  have Hb:=hmtw.exists_local_branch_jet_bound_second hlam hcap
    (reverseRay_minimizing hmin) hG hagree hl
  simp only [reverseRay_base,reverseRay_endpoint] at Hb
  obtain ⟨N,hN,C,hC,HN⟩:=Hb
  have hχleft:χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hχsym:ContinuousAt χ.symm (χ z) := continuousAt_extChartAt_symm'' (mem_extChartAt_target z)
  have hχlim:Tendsto χ.symm (𝓝 (χ z)) (𝓝 z) := by simpa only [hχleft] using hχsym.tendsto
  have hAct:∀ᶠ q in 𝓝 (χ z),G (riemannianExp (χ.symm q).1 (χ.symm q).2,(χ.symm q).1)=‖(χ.symm q).2‖^2/2 :=
    hχlim.eventually hact
  obtain ⟨V,hV,hVo,hVz⟩:=mem_nhds_iff.mp (inter_mem hW hAct)
  have hVe:V⊆e.source := fun q hq=>hWe (hV hq).1
  let J:=fun q:(Model n×Model n)×ℝ=>(((e q.1).2,(χ.symm q.1).1),q.2)
  have hJ:ContinuousAt J (χ z,l) := by
    have hE : ContinuousAt (fun q : (Model n × Model n) × ℝ => e q.1) (χ z,l) :=
      (e.continuousAt hze).comp (x := (χ z,l)) (f := Prod.fst) continuousAt_fst
    have hχ : ContinuousAt (fun q : (Model n × Model n) × ℝ => χ.symm q.1) (χ z,l) :=
      hχsym.comp (x := (χ z,l)) (f := Prod.fst) continuousAt_fst
    have hb := (FiberBundle.continuous_proj (Model n)
      (TangentSpace 𝓘(ℝ,Model n))).continuousAt.comp hχ
    exact (hE.snd.prodMk hb).prodMk continuousAt_snd
  have hJ0:J (χ z,l)=((d (riemannianExp z.1 z.2),z.1),l) := by
    dsimp only [J]
    rw [he]
    dsimp only
    rw [hχleft]
  let U:=Prod.fst ⁻¹' V ∩ J ⁻¹' N
  have hU:U∈𝓝 (χ z,l) := inter_mem
    (continuous_fst.continuousAt.preimage_mem_nhds (hVo.mem_nhds hVz))
    (hJ.preimage_mem_nhds (by rwa [hJ0]))
  refine ⟨U,hU,C*K,mul_nonneg hC hK,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc B hB hjet ξ
  let r:=χ.symm q.1
  let v:=fun w:Model n=>φ (uv.2 (d.symm w))+G (d.symm w,r.1)
  have hqe:q.1∈e.source := hVe hq.1
  have hepoint:d.symm (e q.1).2=riemannianExp r.1 r.2 := by
    rw [he]
    exact d.left_inv (hes q.1 hqe)
  have HEq:(fun δ:Model n=>v ((e (q.1.1,q.1.2+δ)).2)) =ᶠ[𝓝 0]
      (fun δ=>let s:=χ.symm (q.1.1,q.1.2+δ)
        φ (uv.2 (riemannianExp s.1 s.2))+‖s.2‖^2/2) := by
    have ht:ContinuousAt (fun δ:Model n=>(q.1.1,q.1.2+δ)) 0 :=
      continuousAt_const.prodMk (continuousAt_const.add continuousAt_id)
    have hv0:(q.1.1,q.1.2+(0:Model n))∈V := by simpa only [add_zero,Prod.eta] using (show q.1∈V from hq.1)
    filter_upwards [ht.preimage_mem_nhds (hVo.mem_nhds hv0)] with δ hδ
    have hδe:=hVe hδ
    have haδ: G (riemannianExp (χ.symm (q.1.1,q.1.2+δ)).1 (χ.symm (q.1.1,q.1.2+δ)).2,
        (χ.symm (q.1.1,q.1.2+δ)).1)=‖(χ.symm (q.1.1,q.1.2+δ)).2‖^2/2 := (hV hδ).2
    dsimp only [v]
    rw [he]
    dsimp only
    rw [d.left_inv (hes _ hδe)]
    have hb:(χ.symm (q.1.1,q.1.2+δ)).1=r.1 := rfl
    rw [hb] at haδ
    congr 1
  have hjet':HasLowerSecondTaylor (fun δ:Model n=>v ((e (q.1.1,q.1.2+δ)).2)) 0 B :=
    hjet.mono HEq.eq_of_nhds.symm HEq.symm.le
  apply HK q.1 (hV hq.1).1 v B hjet' hB C hC _ ξ
  intro H hH hHjet η
  apply HN (J q) hq.2 x0 uv huv φ hmono _ _ _ H hH _ η
  · change ContDiffAt ℝ 2 φ (uv.2 (d.symm (e q.1).2))
    rw [hepoint]
    exact hφ
  · change HasDerivAt φ q.2 (uv.2 (d.symm (e q.1).2))
    rw [hepoint]
    exact hd
  · change iteratedDeriv 2 φ (uv.2 (d.symm (e q.1).2)) ≤ 0
    rw [hepoint]
    exact hconc
  · exact hHjet

end LocalOuterLog
end WeakMTWTransport

end
end

end OAI

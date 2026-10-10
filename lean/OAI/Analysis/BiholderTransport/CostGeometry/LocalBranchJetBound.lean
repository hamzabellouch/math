import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SmoothSupportSemibound
import OAI.Analysis.BiholderTransport.Coordinates.BranchChartBaseline
import OAI.Analysis.BiholderTransport.Coordinates.BranchChartJets
import OAI.Analysis.BiholderTransport.Coordinates.LocalOuterJetBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalBranchJetBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_branch_jet_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0≤cap) {a:M}
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl : 1<l) :
    let c := fun y:M => fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,y)
    ∃ U : Set ((Model n×M)×ℝ),
      U∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,riemannianExp a r),l) ∧ ∃ C≥0,
      ∀ q∈U,∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ:ℝ → ℝ,StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) →
      HasDerivAt φ q.2 (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) →
      iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))≤0 →
      ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
      HasLowerSecondTaylor (fun h =>
        φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (q.1.1+h)))+c q.1.2 (q.1.1+h)) 0 H →
      ∀ d,H d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := riemannianExp a r
  let q0 : (Model n×M)×ℝ := ((z,b),l)
  let c := fun y:M => fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,y)
  obtain ⟨hc,L,hcD,hpreg,m,hm,Hm⟩ := exists_branch_chart_baseline hr hG hagree hl
  have hlp : 0<l := zero_lt_one.trans hl
  let δ := m/(4*(l+1))
  have hδ : 0<δ := div_pos hm (by positivity)
  obtain ⟨N,hN,C,hC,HC⟩ := hmtw.exists_local_outer_chart_jet_bound hlam hcap a L hpreg hδ
    (show 0<l+1 by positivity)
  have ha : z∈(extChartAt 𝓘(ℝ,Model n) a).target := mem_extChartAt_target a
  have hGa : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      ((extChartAt 𝓘(ℝ,Model n) a).symm z,b) := by
    simpa only [z,b,(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)] using hG
  obtain ⟨hD,hH,hcnear⟩ := branch_chart_jet_continuous ha hGa
  let P := fun q:(Model n×M)×ℝ => q.2⁻¹ • (-fderiv ℝ (c q.1.2) q.1.1)
  have hP0 : P q0=L := by
    dsimp only [P,q0,c,z,b]
    rw [hcD]
    ext d
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_mul,neg_neg]
    field_simp [hlp.ne']
  have hP : ContinuousAt P q0 :=
    (continuousAt_snd.inv₀ hlp.ne').smul ((hD.comp (x := q0) (f := fun q : (Model n×M)×ℝ => q.1) continuousAt_fst).neg)
  let J := fun q:(Model n×M)×ℝ => (q.1.1,P q)
  have hJ : ContinuousAt J q0 := (continuousAt_fst.comp continuousAt_fst).prodMk hP
  have hJ0 : J q0=(z,L) := by simp only [J,q0,hP0]
  let Y := fun q:(Model n×M)×ℝ => coordinateBackward a (-1,q.1.1,P q)
  have hY : ContinuousAt Y q0 :=
    ((coordinateBackward_contMDiffAt (q := (-1,z,P q0)) ha).continuousAt).comp (x := q0)
      (f := fun q : (Model n×M)×ℝ => (-1,q.1.1,P q)) (continuousAt_const.prodMk hJ)
  have hY0 : Y q0=coordinateBackward a (-1,z,L) := by simp only [Y,q0,hP0]
  have hcost : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,Y q0) := by
    rw [hY0,coordinateBackward_eq_exp_chartGradient ha]
    exact cost_contMDiffAt_of_injectivityDomain
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ : TangentBundle 𝓘(ℝ,Model n) M) hpreg
  have htrue := (chartCost_jet_continuous ha hcost).1.comp (x := q0)
    (f := fun q : (Model n×M)×ℝ => (q.1.1,Y q))
    ((continuousAt_fst.comp continuousAt_fst).prodMk hY)
  let W := fun q:(Model n×M)×ℝ =>
    q.2 • fderiv ℝ (fderiv ℝ (chartCost a (Y q))) q.1.1-fderiv ℝ (fderiv ℝ (c q.1.2)) q.1.1
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hW : ContinuousAt W q0 := (continuousAt_snd.smul htrue).sub (hH.comp (x := q0) (f := fun q : (Model n×M)×ℝ => q.1) continuousAt_fst)
  have hW0 (d:Model n) : m*‖d‖^2≤W q0 d d := by
    dsimp only [W,q0]
    rw [hY0]
    exact Hm d
  let U := {q:(Model n×M)×ℝ | J q∈N ∧ 0<q.2 ∧ q.2≤l+1 ∧
    ContDiffAt ℝ 2 (c q.1.2) q.1.1 ∧ ‖W q-W q0‖< m/2}
  have hU : U∈𝓝 q0 := by
    have hn := hJ.preimage_mem_nhds (by rwa [hJ0])
    have hnW : ∀ᶠ q in 𝓝 q0,‖W q-W q0‖< m/2 := by
      filter_upwards [hW.tendsto.eventually
        (Metric.ball_mem_nhds (W q0) (show 0 < m/2 by positivity))] with q hq
      change dist (W q) (W q0) < m/2 at hq
      rwa [dist_eq_norm (W q) (W q0)] at hq
    filter_upwards [hn,continuousAt_snd.preimage_mem_nhds (lt_mem_nhds hlp),
      continuousAt_snd.preimage_mem_nhds (gt_mem_nhds (show l<l+1 by linarith)),
      continuousAt_fst.tendsto.eventually hcnear,hnW] with q hq hp hu hs hw
    exact ⟨hq,hp,hu.le,hs,hw⟩
  refine ⟨U,hU,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc H hHjet hjet d
  obtain ⟨hqN,hqpos,hqmax,hqc,hqW⟩ := hq
  have hbase (e:Model n) : 2*δ*q.2*‖e‖^2≤W q e e := by
    have Hb := hW0 e
    have Habs := (abs_le.mp (bilinear_diag_sub_bound (W q) (W q0) e)).1
    have Hsmall := mul_le_mul_of_nonneg_right hqW.le (sq_nonneg ‖e‖)
    have Hl : 2*δ*q.2≤ m/2 := by
      calc
        _ ≤ 2*δ*(l+1) := mul_le_mul_of_nonneg_left hqmax (by positivity)
        _ = m/2 := by dsimp [δ]; field_simp [show l+1≠0 by positivity]; ring
    have Hδ := mul_le_mul_of_nonneg_right Hl (sq_nonneg ‖e‖)
    nlinarith only [Hb,Habs,Hsmall,Hδ]
  exact HC x0 uv huv q.1.1 (c q.1.2) q.2 hqpos hqmax hqc hqN hbase
    φ hmono hφ hd hconc H hHjet hjet d

end LocalBranchJetBound
end WeakMTWTransport

end

end

end

end OAI

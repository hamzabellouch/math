import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumPhaseCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumTrueCenter
import OAI.Analysis.BiholderTransport.Regularity.MaximumOuterSamples
import OAI.Analysis.BiholderTransport.Regularity.MaximumTrueOuter
import OAI.Analysis.BiholderTransport.Regularity.MaximumPoleCompact
import OAI.Analysis.BiholderTransport.LinearAlgebra.FunctionalCoercive
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSimultaneous
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance simulDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance simulDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma WeakMTW.exists_maximum_simultaneous
    (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃δ:ℝ,δ>0 ∧ ∃K:ℝ,K>0 ∧ ∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀Lv:ℝ≥0,LipschitzWith Lv (uv.2:M → ℝ) → IsCostDualPair (uv.1:M → ℝ) uv.2 →
    ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc → ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    (∀y,uv.2 y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0 < deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y)<1) →
    ∀Klip:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith Klip (modifiedDatum uv.2 α D b Bc)) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0 < χ → 0 < r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) uv.1 χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>uv.2 ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(q:Model n) (β l κc:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=κc →
    l∈U → 0 < l → l<1 → κc<0 →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀CH CL:ℝ,0 ≤ CH → 0 ≤ CL →
    (∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ (J.first k).H d d) →
    (∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ CL*‖d‖^2) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀(e:TangentSpace 𝓘(ℝ,Model n) a) (t lo κo:ℝ),
    ‖e‖=1 → 0 < t → (show TangentSpace 𝓘(ℝ,Model n) a from r i)= (show TangentSpace 𝓘(ℝ,Model n) a from q)+t • e →
    0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e →
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=lo →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κo →
    1 < lo → κo<0 →
    ∃rc:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from rc)∈minimizingVectors c ∧
      reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
    ∃V W:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d e,W d e=W e d) ∧ (∀d,d≠0 → 0 < W d d) ∧
      0 < expJacobian c rc ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c rc*(bilinearOperator V).det ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator W).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
          (expJacobian (n:=n) a (r i))^2 ∧
      (-κo/lo^2)*(m i)^(n-1)*(bilinearOperator V).det≤(-κc/l^2)*(bilinearOperator W).det := by
  classical
  let : NeZero n:=⟨Nat.ne_of_gt hn⟩
  obtain ⟨δ,hδ,U,hU,h1,HC⟩:=exists_maximum_true_center (n:=n) (M:=M)
  obtain ⟨K,hK,HO⟩:=hmtw.exists_maximum_true_outer hlam hcap
  refine ⟨δ,hδ,K,hK,U,hU,h1,?_⟩
  intro x0 uv huv Lv hv hd α D bminus bplus A₀ B₀ Bc Bo ho hBc hBo hmono hmonoO
    hrange hslope Klip hLip F a c χ N r₀ hχ hr₀ hgood J q β l κc hq he hQ hβ hdC hddC
    hlu hl hl1 hκc r m L hr hm hL CH CL hCH hCL hH hCLbd i hri hmi e t lo κo he1 ht hriq
    hqe hdO hddO hlo hκo
  let ε:=fun k:ℕ=>1/((k:ℝ)+1)
  have hε:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S⟩:=J.exists_outer_diagonal (show ∀k,0 < ε k by intro k; dsimp [ε]; positivity)
  have hreg:=J.center_regular uv.1.continuous hv hd hBc hmono Klip hLip hq he hQ hβ hdC hl hl1
  obtain ⟨g,H,σ,hσ,hg,hHs⟩:=S.center_phase_compact hε hreg he hQ hCH hCL hH hCLbd
  let σt:=hσ.tendsto_atTop
  let J':=J.comp σ σt
  let S':=S.comp σ σt
  obtain ⟨rc,hrc,hrev,V,hVs,hVp,hgain,hσc,hdetC⟩:=HC uv.1 uv.2 uv.1.continuous Lv hv hd
    α D bminus bplus A₀ B₀ Bc Bo ho hBc hmono hrange hslope Klip hLip hmtw
    (F.comp σ σt) a c χ N r₀ hχ hr₀ hgood J' (ε ∘ σ) _ S' (hε.comp σt)
    q β l hq he (hQ.comp σt) (hβ.comp σt) hdC hlu hl hl1 g H L hg hHs (hL.comp σt)
  obtain ⟨_,hp,_,_⟩:=F.limit_coordinates hQ
  obtain ⟨hLp,hLs,hker⟩:=J.pole_limit_properties hL hp hr
  have hke:∀d:Model n,L (show Model n from e) d=0:=by
    intro d
    have hh:=hker i d
    have hriq' : r i = q+t • (show Model n from e) := hriq
    have heq:r i-q=t • (show Model n from e):=by
      rw [hriq',add_sub_cancel_left]
    rw [heq,map_smul,smul_apply,smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left ht.ne'
  let f:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q
  let gO:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i)
  have hf:0 < f (show Model n from e):=by
    calc
      0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e := hqe
      _ = f (show Model n from e) := (frameMetric_center a q (show Model n from e)).symm
  have hfg:f (show Model n from e)≤gO (show Model n from e):=by
    calc
      f (show Model n from e) = inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e :=
        frameMetric_center a q (show Model n from e)
      _ ≤ inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from r i) e := by
        rw [hriq,inner_add_left,inner_smul_left,real_inner_self_eq_norm_sq,he1]
        simp only [one_pow,mul_one,starRingEnd_apply,star_trivial]
        linarith only [ht]
      _ = gO (show Model n from e) := (frameMetric_center a (r i) (show Model n from e)).symm
  have hVL:∀d:Model n,V d d≤L d d+(-κc/l^2)*(f d)^2:=by
    intro d
    have HH:=hgain d
    rw [hddC] at HH
    have hpG:0 ≤ δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d:=by
      rw [frameMetric_center,real_inner_self_eq_norm_sq]
      positivity
    dsimp only [f]
    simp only [neg_div, neg_mul]
    linarith only [HH,hpG]
  have hbc:0 <  -κc/l^2:=div_pos (neg_pos.mpr hκc) (sq_pos_of_pos hl)
  have hbo:0 <  -κo/lo^2:=div_pos (neg_pos.mpr hκo) (sq_pos_of_pos (zero_lt_one.trans hlo))
  have hbase:=functional_rank_one_positive hLs hLp hVp hVL hke hf.ne'
    (hf.trans_le hfg).ne' hmi hbo
  obtain ⟨W,hWs,hWp,hW,hdetO⟩:=HO x0 uv huv α D bminus bplus Bc Bo ho hBo hmonoO
    (F.comp σ σt) a c N J' (ε ∘ σ) S' (hε.comp σt) q β he (hQ.comp σt) (hβ.comp σt)
    r m L (hr.comp σt) (hm.comp σt) (hL.comp σt) i hri hmi lo κo hdO hddO hlo hκo (by
      intro d hd
      have HH:=hbase d hd
      dsimp only [gO] at HH
      simpa only [neg_div, neg_mul, sub_eq_add_neg] using HH)
  have hdet:=bilinear_determinant_gain hLs hVs hWs hke hf hfg hmi hbc hbo hVp hVL (by
    intro d
    have HH:=hW d
    dsimp only [gO]
    simpa only [neg_div, neg_mul, sub_eq_add_neg] using HH)
  refine ⟨rc,hrc,hrev,V,W,hVs,hVp,hWs,hWp,hσc,hdetC,hdetO,?_⟩
  simpa only [Model,finrank_euclideanSpace,Fintype.card_fin] using hdet
end MaximumSimultaneous
end WeakMTWTransport

end
end

end OAI

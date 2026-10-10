import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MaximumRank
import OAI.Analysis.BiholderTransport.Regularity.FirstOutward

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumFamily.positive_excess
    {v:M → ℝ} {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ}
    (F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo)
    (hm:0 ≤ bminus) (hp:0 < bplus) (k:ℕ) :
    0 < modifiedExcess v α D (F.b k) Bc Bo
      (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) := by
  have h0:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have hpen:0 ≤ parameterPenalty bplus (F.b k):=by
    unfold parameterPenalty
    positivity
  have H:=F.positive k
  rw [(F.row k).value] at H
  linarith only [H,hpen]

lemma MaximumJensenFamily.eventual_outward
    {hmtw:WeakMTW (n:=n) (M:=M)} {u v:M → ℝ}
    (hu:Continuous u) {hv:Continuous v} (hdual:IsCostDualPair u v)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation u v (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D) :
    ∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
      let P:=chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp x (chartFiberInverse a b ((J.first k).pj₀ i)))-α)/D
      ∃e:TangentSpace 𝓘(ℝ,Model n) x,∃i:Fin (Module.finrank ℝ (Model n)+1),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ a0*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        chartFiberInverse a b ((J.first k).pj₀ i)=P+d • e ∧
        (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ (J.first k).w₀ i ∧
        (1/4096)*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
        Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) := by
  have HR:=J.eventual_rank_of_center_lower hm hp hprofiles hQ hA hH
  filter_upwards [HR] with k hk
  dsimp only at hk ⊢
  obtain ⟨e,hes,he,hpe,hline,hgain⟩:=hk
  have hqa':a0*D ≤ (inner ℝ
      (chartFiberInverse a (graphBaseCoordinate a (F.row k).q.1)
        (graphVelocityCoordinate a (F.row k).q.1)) e)^2:=by
    apply (mul_le_mul_iff_right₀ (neg_pos.mpr hC)).mp
    nlinarith only [hgain,hqa]
  have hbt:graphBaseCoordinate a (F.row k).q.1∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have hrec:=graph_coordinate_reconstruction (J.poleSource k)
  have hx: (extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a (F.row k).q.1)=
      (F.row k).q.1.1:=congrArg Bundle.TotalSpace.proj hrec
  have hept:riemannianExp
      ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a (F.row k).q.1))
      (chartFiberInverse a (graphBaseCoordinate a (F.row k).q.1)
        (graphVelocityCoordinate a (F.row k).q.1))=
      riemannianExp (F.row k).q.1.1 (F.row k).q.1.2:=
    congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2) hrec
  have hb:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have hparam:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
  dsimp only at hparam
  simp only [movingNormal_eq hbt] at hparam
  have hpn:(1:ℝ)/4096 ≤ (1:ℝ)/4096+4*F.b k/bplus:=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hb) hp.le)
  obtain ⟨i,d,_,hd,hpd,hmi,hmom,hdmax,hsi,hsi',hcap,_,_⟩:=
    (J.first k).outward_endpoint hmtw hu hv hdual ho hb hob hcb hright e he hpe hline
      (1/4096) eta delta zeta a0 hD (by norm_num) ha0 hqa' heta hdelta hdeltaEta hzeta hleft
      (by rw [hept]; exact F.positive_excess hm hp k) (herror k)
      (by rw [hx]; exact hosc k) (hpn.trans hparam)
  exact ⟨e,i,d,he,hpe,hqa',hd,hpd,hmi,hmom,hdmax,hsi,hsi',hcap⟩

end MaximumOutward
end WeakMTWTransport

end
end

end OAI

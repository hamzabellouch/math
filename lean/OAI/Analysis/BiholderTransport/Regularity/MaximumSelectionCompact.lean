import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumPoleCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumOutward
import OAI.Analysis.BiholderTransport.Regularity.MaximumOutwardCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumOuterBound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSelectionCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.selected_pole_compact
    {hmtw:WeakMTW (n:=n) (M:=M)} {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
    {F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)}
    (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
    (hd:IsCostDualPair (uv.1:M → ℝ) uv.2)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {q:Model n} {β:ℝ} (hβ:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
      C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation uv.1 uv.2 (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D)
    (hmono:∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s)))
    (hmargin:∀s:ℝ,-2*eta ≤ s → s ≤ 1-eta →
      Bo s ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) →
      1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
      iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
    ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃CL:ℝ,0 ≤ CL ∧
    ∃i:Fin (Module.finrank ℝ (Model n)+1),
      Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
      Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
      Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) ∧
      (∀ᶠ k in atTop,∀d,(J.first (σ k)).L d d ≤ CL*‖d‖^2) ∧
      (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈minimizingVectors a) ∧
      (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧
      (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ m i ∧
      -2*eta ≤ (uv.2 (riemannianExp a (r i))-α)/D ∧
      (uv.2 (riemannianExp a (r i))-α)/D ≤ 1-eta ∧
      Bo ((uv.2 (riemannianExp a (r i))-α)/D) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) ∧
      ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
        (show TangentSpace 𝓘(ℝ,Model n) a from r i)=
          (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
        0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
        a0*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
        ‖show TangentSpace 𝓘(ℝ,Model n) a from r i‖^2-
          ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*a0))*D := by
  have hsel:=J.eventual_outward uv.1.continuous hd hm hp hprofiles hob hcb hright hQ hA hC
    hH hD ha0 hqa heta hdelta hdeltaEta hzeta hleft herror hosc
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  let ν:ℝ:=(1/4096)/(8*(Module.finrank ℝ (Model n)+1:ℝ))
  have hμ:0 < μ:=by dsimp [μ]; positivity
  have hν:0 < ν:=by dsimp [ν]; positivity
  obtain ⟨σ,hσ,r,m,i,hr,hm',ha,hmn,hmt,hbar,hmi,hmi',hs,hs',hcapO,e,d,he,hd',hri,hpe,hpD,hmom,hdmax,hgap⟩:=
    J.active_outward_compact hβ hQ hμ hν ha0 hD (by
      filter_upwards [hsel] with k hk
      obtain ⟨e,i,d,he,hpe,hpD,hd,hri,hmi,hmom,hdmax,hs,hs',hcapO⟩:=hk
      refine ⟨i,e,d,he,hpe,hpD,hd,hri,hmi,?_,hdmax,hs,hs',hcapO⟩
      dsimp only [ν]
      convert! hmom using 1
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring)
  have hβmem:β∈Icc bminus bplus:=isClosed_Icc.mem_of_tendsto hβ
    (Eventually.of_forall (fun k=>Ioo_subset_Icc_self (F.parameter k)))
  have hz:α+D*((uv.2 (riemannianExp a (r i))-α)/D)=uv.2 (riemannianExp a (r i)):=by
    field_simp [hD.ne']
    ring
  have hmar:=hmargin _ hs hs' hcapO
  rw [hz] at hmar
  let J':=J.comp σ hσ.tendsto_atTop
  obtain ⟨CL,hCL,HCL⟩:=J'.outer_bound hlam hcap huv ho (hβ.comp hσ.tendsto_atTop)
    ((F.limit_coordinates hQ).1.comp hσ.tendsto_atTop) (fun _=>i)
    (tendsto_pi_nhds.mp hr i) hμ hmi'
    (fun k=>hmono _ (Ioo_subset_Icc_self (F.parameter (σ k)))) (hmono β hβmem) hmar.1 hmar.2
  obtain ⟨L,τ,hτ,hL⟩:=J'.pole_compact hCL HCL
  refine ⟨σ ∘ τ,hσ.comp hτ,r,m,L,CL,hCL,i,hr.comp hτ.tendsto_atTop,
    hm'.comp hτ.tendsto_atTop,hL,hτ.tendsto_atTop.eventually HCL,?_,hmn,hmt,hbar,hmi,
    hs,hs',hcapO,e,d,he,hd',hri,hpe,hpD,hgap⟩
  intro j
  exact (ha j).1

end MaximumSelectionCompact
end WeakMTWTransport

end
end

end OAI

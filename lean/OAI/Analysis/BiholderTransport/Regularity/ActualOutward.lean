import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ActiveDifference
import OAI.Analysis.BiholderTransport.Regularity.ActualLevels

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ActualOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actual_outward_endpoint (hmtw:WeakMTW (n := n) (M := M))
    {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hdual:IsCostDualPair u v)
    {α D b H:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo) (hb:0 ≤ b)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {ι:Type} [Fintype ι] [DecidableEq ι] {N:ℕ} (hN:Fintype.card ι ≤ N+1)
    {x:M} {p e:TangentSpace 𝓘(ℝ,Model n) x}
    {pj:ι → TangentSpace 𝓘(ℝ,Model n) x} {m:ι → ℝ}
    (hm:∀i,0 < m i) (hsum:∑ i,m i=1) (hbar:∑ i,m i • pj i=p)
    (hactive:∀i,pj i∈activeLogs (modifiedDatum v α D b Bo) x)
    (he:‖e‖=1) (hq:0  <  inner ℝ p e)
    (hline:Submodule.span ℝ (range (fun i=>pj i-p))=Submodule.span ℝ {e})
    {c eta delta zeta a0:ℝ} (hD:0 < D) (hc:0 < c) (ha0:0 < a0)
    (hqa:a0*D ≤ (inner ℝ p e)^2) (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta)
    (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (hexcess:0 < modifiedExcess v α D b Bc Bo (riemannianExp x p))
    (herror:2*(H+2)*b ≤ zeta*D)
    (hosc:sectionOscillation u v x ((H+2)*b) ≤ (1+delta)*D)
    (hparameter:c ≤ Bc ((v (riemannianExp x p)-α)/D)-
      ∑ i,m i*Bo ((v (riemannianExp x (pj i))-α)/D)) :
    let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
    let mstar:=c/(12*(N+1:ℝ))
    let theta0:=min (mstar/2) (a0/3)
    ∃ i d,0 < d ∧ pj i=p+d • e ∧ mstar ≤ m i ∧
      c*D/(8*(N+1:ℝ)*(inner ℝ p e)) ≤ m i*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      Bo (si i) ≤ 12*(N+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        p+theta • (pj i-p)∈convexHull ℝ (range pj) ∧
        (inner ℝ p e)/2 ≤ inner ℝ (p+theta • (pj i-p)) e ∧
        ‖pj i-p‖^2/(inner ℝ (p+theta • (pj i-p)) (pj i-p)) ≤ 3/a0 := by
  dsimp only
  let y:=riemannianExp x p
  let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
  let s:=(v y-α)/D
  have hp:p∈convexHull ℝ (activeLogs (modifiedDatum v α D b Bo) x) := by
    rw [←hbar]
    exact (convex_convexHull ℝ _).sum_mem (fun i _=>(hm i).le) hsum
      (fun i _=>subset_convexHull ℝ _ (hactive i))
  obtain ⟨hy,Hlevels⟩:=hmtw.modified_aligned_levels hu hv hdual ho hb hob hcb hp
  have hH:0 ≤ H:=(hob 0).1.trans (hob 0).2
  have hr:0 ≤ (H+2)*b:=mul_nonneg (by linarith) hb
  have hrange:∀i j,|si i-si j| ≤ 1+delta := fun i j=>
    section_level_range hv hdual hr hD (Hlevels (pj i) (hactive i)).1
      (Hlevels (pj j) (hactive j)).1 hosc
  have hcenter:∀i,|s-si i| ≤ 1+delta := fun i=>
    section_level_range hv hdual hr hD hy (Hlevels (pj i) (hactive i)).1 hosc
  have hlow:=limiting_levels_lower (fun i=>(hm i).le) hsum (fun r=>(hob r).1) hleft
    (hcb s).2 hc hparameter hrange hcenter hdeltaEta
  have hs:s < 3/4:=modified_positive_excess_center_level hu hv hdual ho hb
    (fun r=>(hob r).1) hright hexcess
  have herr:∀i,|‖pj i‖^2-‖p‖^2+2*D*(si i-s)| ≤ zeta*D := by
    intro i
    have Hlev: v (riemannianExp x (pj i))-v y=(‖p‖^2-‖pj i‖^2)/2+
        b*(Bc s-Bo (si i))-modifiedExcess v α D b Bc Bo y :=
      (Hlevels (pj i) (hactive i)).2
    have Hdiv:D*(si i-s)=v (riemannianExp x (pj i))-v y := by
      dsimp only [si,s]
      field_simp
      ring
    have Hup:=modified_excess_upper (a := α) (D := D) hu hv hdual ho hb (fun r=>(hob r).1)
      (fun r=>(hcb r).2) y
    have Hcb:=mul_le_mul_of_nonneg_left (hcb s).1 hb
    have Hct:=mul_le_mul_of_nonneg_left (hcb s).2 hb
    have Hob:=mul_le_mul_of_nonneg_left (hob (si i)).2 hb
    have Hoz:=mul_nonneg hb (hob (si i)).1
    have hHb:=mul_nonneg hH hb
    apply abs_le.mpr
    constructor  <;>  nlinarith only [Hlev,Hdiv,Hup,hexcess,Hcb,Hct,Hob,Hoz,herror,hHb,hb]
  apply outward_active_endpoint hN hm hsum hbar he hq hline hD hc ha0 hqa heta hdelta hzeta
    hs hlow.2 ?_ herr (fun i=>(hob (si i)).1) (fun i=>hleft (si i)) (hcb s).2 hparameter
  intro i
  simpa only [abs_sub_comm] using hcenter i

end ActualOutward
end WeakMTWTransport

end
end

end OAI

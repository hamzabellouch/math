import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartFirstMatrix
import OAI.Analysis.BiholderTransport.Regularity.ActualOutward

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FirstOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma ChartFixedPrefixLimit.outward_endpoint
    (hmtw:WeakMTW (n := n) (M := M))
    {u v G:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hdual:IsCostDualPair u v)
    {α D β H:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo) (hβ:0 ≤ β)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {a:M} {t:ℝ} {q:ℕ → subgradientGraph (n := n) (cTransform (modifiedDatum v α D β Bo))}
    {q₀:subgradientGraph (n := n) (cTransform (modifiedDatum v α D β Bo))}
    (J:ChartFixedPrefixLimit a (modifiedDatum v α D β Bo) G t q q₀) :
    let b:=graphBaseCoordinate a q₀.1
    let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
    let E:=TangentSpace 𝓘(ℝ,Model n) x
    let P:E:=chartFiberInverse a b (graphVelocityCoordinate a q₀.1)
    let pj:=fun i=>chartFiberInverse a b (J.pj₀ i)
    let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < J.w₀ i}
    ∀ e:E,‖e‖=1 → 0 < inner ℝ P e →
    Submodule.span ℝ (range (fun i:κ=>pj i-P))=Submodule.span ℝ {e} →
    ∀ c eta delta zeta a0:ℝ,0 < D → 0 < c → 0 < a0 →
    a0*D ≤ (inner ℝ P e)^2 → eta ≤ 1/128 → delta ≤ zeta → delta ≤ eta → zeta ≤ 1/16 →
    (∀s,s < 1-eta → 1 ≤ Bo s) →
    0 < modifiedExcess v α D β Bc Bo (riemannianExp x P) →
    2*(H+2)*β ≤ zeta*D → sectionOscillation u v x ((H+2)*β) ≤ (1+delta)*D →
    c ≤ Bc ((v (riemannianExp x P)-α)/D)-∑ i,J.w₀ i*Bo ((v (riemannianExp x (pj i))-α)/D) →
    let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
    let mstar:=c/(12*(Module.finrank ℝ (Model n)+1:ℝ))
    let theta0:=min (mstar/2) (a0/3)
    ∃ i d,0 < J.w₀ i ∧ 0 < d ∧ pj i=P+d • e ∧ mstar ≤ J.w₀ i ∧
      c*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ J.w₀ i*d ∧
      d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        P+theta • (pj i-P)∈convexHull ℝ (activeLogs (modifiedDatum v α D β Bo) x) ∧
        (inner ℝ P e)/2 ≤ inner ℝ (P+theta • (pj i-P)) e ∧
        ‖pj i-P‖^2/(inner ℝ (P+theta • (pj i-P)) (pj i-P)) ≤ 3/a0 := by
  dsimp only
  intro e he hq hline c eta delta zeta a0 hD hc ha0 hqa heta hdelta hdeltaEta hzeta
    hleft hexcess herror hosc hparameter
  classical
  let b:=graphBaseCoordinate a q₀.1
  let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let P:=chartFiberInverse a b (graphVelocityCoordinate a q₀.1)
  let pj:=fun i=>chartFiberInverse a b (J.pj₀ i)
  let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < J.w₀ i}
  have hr:=positive_barycentric_restriction pj J.w₀ J.nonnegLimit J.totalLimit
  have hbar:∑ i:κ,J.w₀ i • pj i=P := by
    rw [hr.2.2.1]
    change ∑ i,J.w₀ i • chartFiberInverse a b (J.pj₀ i)=P
    simp only [←map_smul]
    rw [←map_sum,J.baryLimit]
  have hN:Fintype.card κ ≤ Module.finrank ℝ (Model n)+1 := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)
  have hparam:c ≤ Bc ((v (riemannianExp x P)-α)/D)-
      ∑ i:κ,J.w₀ i*Bo ((v (riemannianExp x (pj i))-α)/D) := by
    rw [hr.2.2.2 (fun i=>Bo ((v (riemannianExp x (pj i))-α)/D))]
    exact hparameter
  obtain ⟨i,d,hd,hpd,hm,hmom,hdmax,hsi,hsi',hcap,htheta,Htheta⟩:=
    hmtw.actual_outward_endpoint hu hv hdual ho hβ hob hcb hright hN
      (fun i:κ=>i.2) hr.2.1 hbar (fun i=>J.activeLimit i)
      he hq hline hD hc ha0 hqa heta hdelta hdeltaEta hzeta hleft hexcess herror hosc hparam
  refine ⟨i.1,d,i.2,hd,hpd,hm,hmom,hdmax,hsi,hsi',hcap,htheta,?_⟩
  intro theta htheta
  obtain ⟨hconv,hq',hratio⟩:=Htheta theta htheta
  refine ⟨convexHull_mono ?_ hconv,hq',hratio⟩
  rintro _ ⟨j,rfl⟩
  exact J.activeLimit j

end FirstOutward
end WeakMTWTransport

end
end

end OAI

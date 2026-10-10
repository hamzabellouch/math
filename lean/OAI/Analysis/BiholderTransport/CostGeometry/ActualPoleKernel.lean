import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.SplitEndpointCost
import OAI.Analysis.BiholderTransport.Contact.ActualPoleJet

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actualPole_kernel (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (ht1 : t<1) (hs : 0<s) (hs1 : s<1) {x:M}
    {p pj : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hmin : pj∈minimizingVectors x)
    (hactive : contactGap u v x (riemannianExp x pj)=0)
    (hleft : s • pj∈injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,pj⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) : R (pj-p)=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun q => hopfLax t u (riemannianExp x (t • q))
  let B : V×V → ℝ := prefixAction x t
  let D : V → ℝ := fun b => splitEndpointCost x s (b,pj)
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have H := harep.self_of_nhds
    rw [ha0,riemannianExp_zero] at H
    exact H.symm
  have hB : DifferentiableAt ℝ B (0,p) :=
    (prefixAction_contDiffAt hp).differentiableAt (by simp)
  have hBa : ∀ b d:V, fderiv ℝ B (0,p) (b,d) = -inner ℝ p b+t*inner ℝ p d := by
    intro b d
    rw [show (b,d)=((b,0):V×V)+(0,d) by simp,map_add]
    rw [prefixAction_source_gradient ht.ne' hp,prefixAction_endpoint_gradient hp]
  have hD : HasFDerivAt D (-innerSL ℝ pj) 0 := by
    have HD := ((splitEndpointCost_contDiffAt hleft hright).differentiableAt
      (by simp)).hasFDerivAt.comp (f := fun b : V => (b,pj)) 0
        ((hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk (hasFDerivAt_const pj (0:V)))
    apply HD.congr_fderiv
    ext b
    change fderiv ℝ (splitEndpointCost x s) (0,pj) (b,0) = -inner ℝ pj b
    exact splitEndpointCost_source_gradient hs.ne' hleft hright b
  have henv : ∀ᶠ q in 𝓝 p, f q-B (a q,q)=u (riemannianExp x (a q)) := by
    filter_upwards [harep] with q hq
    have H := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • q))
    rw [←hq] at H
    dsimp [f,B,prefixAction]
    linarith
  have hm : IsLocalMin (fun q => f q-B (a q,q)+D (a q)) p := by
    have hpEq := henv.self_of_nhds
    have hc : D 0=cost x (riemannianExp x pj) := by
      change splitEndpointCost x s (0,pj)=cost x (riemannianExp x pj)
      rw [splitEndpointCost_axis hs hs1 hleft hright]
      have H := hmin
      change dist x (riemannianExp x pj)=‖pj‖ at H
      rw [cost,H]
    filter_upwards [henv] with q hq
    rw [hpEq,ha0,riemannianExp_zero,hc,hq]
    have HG := dualPair_gap_nonneg hv hdual (riemannianExp x (a q)) (riemannianExp x pj)
    have HC : cost (riemannianExp x (a q)) (riemannianExp x pj)≤D (a q) :=
      normalCost_le_splitNormalAction x pj (a q) pj hs hs1
    dsimp only [contactGap] at HG hactive
    linarith
  exact pole_kernel_of_active_support ha ha0
    (hmtw.actualPole_first_derivative hu hv hdual ht ht1 hp hpole) hB hBa hD hm
    (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).2.2

end WeakMTWTransport

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ActualPoleJet
import OAI.Analysis.BiholderTransport.Calculus.FiniteTaylor

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
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma single_move_weighted_sum {E : Type*} [Zero E] (w : ι → ℝ) (i : ι)
    (ψ : ι → E → ℝ) (d : E) :
    ∑ j,w j*ψ j (if j=i then d else 0)-∑ j,w j*ψ j 0 =
      w i*(ψ i d-ψ i 0) := by
  rw [←Finset.sum_sub_distrib]
  have he : ∀ j, w j*ψ j (if j=i then d else 0)-w j*ψ j 0 =
      if j=i then w i*(ψ i d-ψ i 0) else 0 := by
    intro j; by_cases hj:j=i <;> simp [hj,mul_sub]
  simp_rw [he]
  simp

lemma WeakMTW.actual_transfer_inequality (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (ht1 : t<1) (hs : 0<s) (hs1 : s<1) {x:M}
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap u v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    (ha : ContinuousAt a p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    let S := fun h : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x =>
      prefixDefect x t p (h.1,w i • h.2)-
        ∑ j,w j*splitDefect x s (pj j) (h.1,if j=i then h.2 else 0)
    let f := fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • (p+w i • d)))-t*(‖p+w i • d‖^2/2)
    let ψ := fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2
    ∀ᶠ d in 𝓝 (0:TangentSpace 𝓘(ℝ,Model n) x),
      S (a (p+w i • d),d)-S 0-(f d-f 0)≤w i*(ψ d-ψ 0) := by
  dsimp only
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let ψ : ι → V → ℝ := fun j d => v (riemannianExp x (pj j+d))+‖pj j+d‖^2/2
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have hlimit := ((continuous_riemannianExp x).continuousAt.comp ha).tendsto.congr' harep
    simpa only [Function.comp_apply, ha0, riemannianExp_zero] using eq_of_tendsto_nhds hlimit
  have hf0 := (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).1
  have hψ0 : ∀ j, ψ j 0 = -u x := by
    intro j
    have H := hactive j
    have hm := hmin j
    change dist x (riemannianExp x (pj j))=‖pj j‖ at hm
    rw [contactGap,cost,hm] at H
    dsimp [ψ]; simp only [add_zero]; linarith
  have hD0 : ∀ j,splitDefect x s (pj j) 0=0 := by
    intro j
    simp only [splitDefect,Prod.fst_zero,Prod.snd_zero,add_zero,
      splitEndpointCost_axis hs hs1 (hleft j) (hright j),sub_self]
  have hB0 : prefixDefect x t p 0=0 := by
    simp only [prefixDefect,Prod.fst_zero,Prod.snd_zero,add_zero,prefixAction_axis hp,sub_self]
  have hq : Tendsto (fun d:V => p+w i • d) (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt,smul_zero,add_zero] using
      (show ContinuousAt (fun d:V => p+w i • d) 0 from by fun_prop)
  filter_upwards [hq.eventually harep] with d hd
  have henv := hmtw.hopfPole_minimizer hu hv hdual ht ht1
    (riemannianExp x (t • (p+w i • d)))
  rw [←hd] at henv
  let a' := a (p+w i • d)
  let δ : ι → V := fun j => if j=i then d else 0
  have hineq : -u (riemannianExp x a')≤∑ j,w j*(splitEndpointCost x s (a',pj j+δ j)+
      v (riemannianExp x (pj j+δ j))) := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left
        (show -u (riemannianExp x a')≤ splitEndpointCost x s (a',pj j+δ j)+
          v (riemannianExp x (pj j+δ j)) from by
          have HG := dualPair_gap_nonneg hv hdual (riemannianExp x a')
            (riemannianExp x (pj j+δ j))
          have HC := normalCost_le_splitNormalAction x (pj j+δ j) a' (pj j+δ j) hs hs1
          dsimp only [contactGap] at HG
          change cost (riemannianExp x a') (riemannianExp x (pj j+δ j))≤
            splitEndpointCost x s (a',pj j+δ j) at HC
          linarith) (hw j))
    simpa only [←Finset.sum_mul,hsum,one_mul] using H
  have hsumψ := single_move_weighted_sum w i ψ d
  have hψsum : ∑ j,w j*ψ j 0 = -u x := by
    simp only [hψ0,←Finset.sum_mul,hsum,one_mul]
  rw [hψsum,hψ0 i] at hsumψ
  have hψi0 := hψ0 i
  dsimp only [ψ] at hψi0
  simp only [add_zero] at hψi0
  have hψi0w := congrArg (fun z:ℝ => w i*z) hψi0
  simp only [Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero,ite_self,
    ←Prod.zero_eq_mk,hD0,mul_zero,Finset.sum_const_zero,hB0,sub_zero,hf0]
  dsimp only [prefixDefect,splitDefect,prefixAction] at *
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib,mul_add] at hineq ⊢
  have Hψ : ∑ j,w j*ψ j (δ j)=
      (∑ j,w j*v (riemannianExp x (pj j+δ j)))+∑ j,w j*(‖pj j+δ j‖^2/2) := by
    dsimp only [ψ]; simp only [mul_add,Finset.sum_add_distrib]
  change (∑ j,w j*ψ j (δ j))- -u x=w i*(ψ i d- -u x) at hsumψ
  rw [Hψ] at hsumψ
  dsimp only [ψ] at hsumψ
  dsimp only [a',δ] at hineq hsumψ
  linarith

end WeakMTWTransport

end

end OAI

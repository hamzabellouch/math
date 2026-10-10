import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ActualTransferInequality
import OAI.Analysis.BiholderTransport.CostGeometry.ActualPoleKernel
import OAI.Analysis.BiholderTransport.Calculus.WeightedDefect

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

lemma WeakMTW.actualPole_residual_taylor (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • (p+d)))-t*(‖p+d‖^2/2))
      0 (-((innerSL ℝ).comp R)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have H := (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).1.sub
    ((norm_square_hasSecondTaylor p).const_mul t)
  have hlin : t • innerSL ℝ p-t • innerSL ℝ p=(0:V →L[ℝ] ℝ) := sub_self _
  have hbil : (t • (innerSL ℝ (E := V))-(innerSL ℝ).comp R)-t • innerSL ℝ =
      -((innerSL ℝ).comp R) := by
    apply ContinuousLinearMap.ext; intro d
    apply ContinuousLinearMap.ext; intro e
    change (t*inner ℝ d e-inner ℝ (R d) e)-t*inner ℝ d e = -inner ℝ (R d) e
    ring
  rw [hlin,hbil] at H
  exact H

lemma WeakMTW.actual_active_lower_jet (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (hts : t<s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0<w j) (hsum : ∑ j,w j=1) (i : ι)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap u v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let p : V := ∑ j,w j • pj j
  have hs : 0<s := ht.trans hts
  have ht1 : t<1 := hts.trans hs1
  have hsub : range pj ⊆ activeLogs v x := by
    rintro _ ⟨j,rfl⟩
    exact ⟨hmin j,by rw [←hdual.1]; exact hactive j⟩
  have hID : ∀ q∈convexHull ℝ (range pj),t • q∈injectivityDomain x := by
    intro q hq
    exact contracted_minimizer_mem_injectivityDomain
      (hmtw.active_hull_global_support hv (convexHull_mono hsub hq)).1 ht ht1
  have hpH : p∈convexHull ℝ (range pj) :=
    (convex_convexHull ℝ (range pj)).sum_mem (fun j _ => (hw j).le) hsum
      (fun j _ => subset_convexHull ℝ _ (mem_range_self j))
  have hp := hID p hpH
  have hkernel : ∀ j, R (pj j-p)=0 := fun j =>
    hmtw.actualPole_kernel hu hv hdual ht ht1 hs hs1 hp (hmin j) (hactive j)
      (hleft j) (hright j) ha ha0 harep
  have hsym := (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).2.2
  obtain ⟨B,hB,hBdiag⟩ := prefixDefect_taylor ht.ne' hp
  have HC := fun j => splitDefect_taylor hs hs1 (hleft j) (hright j)
  choose C hC hCdiag using HC
  obtain ⟨D,hD,hDdiag⟩ := weighted_defect_taylor w pj i hB hC hBdiag hCdiag
  let J : V →L[ℝ] V := w i • ContinuousLinearMap.id ℝ V
  have hres := (hmtw.actualPole_residual_taylor hu hv hdual ht ht1 hp ha ha0 harep).comp_linear J
  have hq : HasFDerivAt (fun d:V => p+w i • d) J 0 := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0:V)).const_smul (w i)).const_add p
  have hA : HasFDerivAt (fun d:V => (a (p+w i • d),d))
      ((R.comp J).prod (ContinuousLinearMap.id ℝ V)) 0 := by
    have HA := (show HasFDerivAt a R (p+w i • (0:V)) from by
      simpa only [smul_zero,add_zero] using ha).comp 0 hq
    exact HA.prodMk (hasFDerivAt_id (𝕜 := ℝ) (0:V))
  have hA0 : (a (p+w i • (0:V)),(0:V))=0 := by
    change (a (p+w i • (0:V)),(0:V))=(0,0)
    rw [smul_zero,add_zero,show a p=0 from ha0]
  have Hineq := hmtw.actual_transfer_inequality hu hv hdual ht ht1 hs hs1 pj w
    (fun j => (hw j).le) hsum i hp hmin hactive hleft hright ha.continuousAt ha0 harep
  have Hlow := lowerTaylor_of_stationary_transfer hD hA hA0 hres (hw i)
    (by simpa only [ContinuousLinearMap.zero_comp,zero_apply,sub_zero,J,
      smul_apply,ContinuousLinearMap.id_apply] using Hineq)
  apply Hlow.mono_diagonal
  intro d
  let r : V := R (J d)
  have horth : ∀ j,inner ℝ r (pj j-p)=0 := by
    intro j
    change inner ℝ (R (J d)) (pj j-p)=0
    rw [hsym,hkernel,inner_zero_right]
  have hQ : 0≤hessianValue x (t • p) r/t-∑ j,w j*(hessianValue x (s • pj j) r/s) := by
    by_cases hr : r=0
    · rw [hr]
      simp only [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian (hleft _),
        map_zero,zero_div,mul_zero,Finset.sum_const_zero,sub_zero,le_refl]
    · exact sub_nonneg.mpr (hmtw.finite_transverse_slack_strict pj w hw hsum hmin ht hts hs1 hID hr horth).le
  change w i*inner ℝ (R d) d ≤ (w i)⁻¹ *
    (D (R (J d),d) (R (J d),d)-(-((innerSL ℝ).comp R)) (J d) (J d))
  rw [hDdiag]
  have hinner : (-((innerSL ℝ).comp R)) (J d) (J d) = -(w i)^2*inner ℝ (R d) d := by
    change -inner ℝ (R (w i • d)) (w i • d)=_
    rw [map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  rw [hinner]
  have H := mul_nonneg (inv_nonneg.mpr (hw i).le) hQ
  have hid : (w i)⁻¹*((w i)^2*inner ℝ (R d) d)=w i*inner ℝ (R d) d := by
    field_simp [(hw i).ne']
  dsimp only [r] at H
  linarith

end WeakMTWTransport

end

end OAI

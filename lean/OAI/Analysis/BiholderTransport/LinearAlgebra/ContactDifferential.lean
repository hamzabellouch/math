import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.AlexandrovDerivative
import OAI.Analysis.BiholderTransport.Contact.AEContacts
import OAI.Analysis.BiholderTransport.Contact.ContactSelection
import OAI.Analysis.BiholderTransport.Convexity.CoordinateSemiconvex
import OAI.Analysis.BiholderTransport.Calculus.Gradient
import OAI.Analysis.BiholderTransport.LinearAlgebra.Aggregate

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_normal_local_inverse_at {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ κ : M → TangentSpace 𝓘(ℝ,Model n) x,
      κ (riemannianExp x p)=p ∧
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ κ (riemannianExp x p) ∧
      ∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (κ y)=y := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hp',hc⟩ := exists_coordinate_exp_inverse hp
  let κ : M → V := fun z => e.symm (d z)
  have hep : e p=d y := congrFun he p
  have hκp : κ y=p := by change e.symm _=p; rw [←hep]; exact e.left_inv hp'
  have hκ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ κ y := by
    apply ContMDiffAt.comp y _ contMDiffAt_extChartAt
    rw [←hep]
    exact hc.contMDiffAt
  refine ⟨κ,hκp,hκ,?_⟩
  have hct : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n)) (n := ∞) (x := y)).continuousAt.preimage_mem_nhds
      (by rw [←hep]; exact e.open_target.mem_nhds (e.map_source hp'))
  have hcs : ∀ᶠ z in 𝓝 y, z∈d.source := extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y
  have hes : ∀ᶠ z in 𝓝 y, riemannianExp x (κ z)∈d.source :=
    (((contMDiff_riemannianExp_fiber x).continuous.continuousAt).comp hκ.continuousAt).preimage_mem_nhds
      (by simp only [Function.comp_apply,hκp]; exact extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y)
  filter_upwards [hct,hcs,hes] with z hzt hzs hzes
  apply d.injOn hzes hzs
  change (fun q => d (riemannianExp x q)) (κ z)=_
  rw [←he]
  exact e.right_inv hzt

def normalHessianOperator (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (normalHessian x p)

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_normalHessianOperator (x : M) (p u v : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (normalHessianOperator x p u) v=normalHessian x p u v := by
  exact InnerProductSpace.toDual_symm_apply

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma prefixNormalCost_source_hessian_full {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x 1)) (0,p) (u,0) (v,0)=normalHessian x p u v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hp1 : (1:ℝ) • p∈injectivityDomain x := by simpa only [one_smul] using hp
  have hsym := (prefixNormalCost_contDiffAt hp1).isSymmSndFDerivAt
    (by simp)
  have heq := symmetric_bilinear_eq_of_diagonal
    (A := (fderiv ℝ (fderiv ℝ (prefixNormalCost x 1)) (0,p)).bilinearComp
      (ContinuousLinearMap.inl ℝ V V) (ContinuousLinearMap.inl ℝ V V))
    (B := normalHessian x p)
    (fun a b => hsym.eq (a,0) (b,0)) (normalHessian_symm hp)
    (fun a => by simpa only [ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.inl_apply,one_smul,div_one] using prefixNormalCost_source_hessian hp1 a)
  exact congrArg (fun D : V →L[ℝ] V →L[ℝ] ℝ => D u v) heq

omit [MeasurableSpace M] [BorelSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma normal_contact_twist {v : M → ℝ} (hv : Continuous v) {x : M}
    {a p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : DifferentiableAt ℝ (prefixNormalCost x 1) (a,p))
    (hcontact : contactGap (cTransform v) v (riemannianExp x a) (riemannianExp x p)=0)
    {g : TangentSpace 𝓘(ℝ,Model n) x}
    (hg : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) (innerSL ℝ g) a) :
    (fderiv ℝ (prefixNormalCost x 1) (a,p)).comp
      (ContinuousLinearMap.inl ℝ _ _)= -(innerSL ℝ g) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hmin : IsLocalMin (fun h : V => cTransform v (riemannianExp x h)+
      prefixNormalCost x 1 (h,p)) a := by
    apply Filter.Eventually.of_forall
    intro h
    have H := cTransform_gap_nonneg hv (riemannianExp x h) (riemannianExp x p)
    simp only [contactGap] at H hcontact
    simp only [prefixNormalCost,one_smul,div_one]
    linarith
  have hd := hB.hasFDerivAt.comp (f := fun h : V => (h,p)) a
    ((hasFDerivAt_id a).prodMk (hasFDerivAt_const p a))
  have hz := hmin.hasFDerivAt_eq_zero (hg.add hd)
  have H : innerSL ℝ g+(fderiv ℝ (prefixNormalCost x 1) (a,p)).comp
      (ContinuousLinearMap.inl ℝ V V)=0 := by simpa only [ContinuousLinearMap.inl] using hz
  exact eq_neg_of_add_eq_zero_right H

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_selection_normal_differential {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x)
    (hpI : p∈injectivityDomain x)
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0) :
    ∃ r>0, ∃ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      q 0=p ∧ ContinuousAt q 0 ∧
      (∀ᶠ h in 𝓝 0, riemannianExp x (q h)=T (riemannianExp x h)) ∧
      HasFDerivWithinAt q (normalHessianOperator x p+A)
        {h | h∈Metric.ball 0 r ∧ DifferentiableAt ℝ (fun z => cTransform v (riemannianExp x z)) h} 0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun h => cTransform v (riemannianExp x h)
  have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv hDiff (hT x) hp.2
  have hTc : ContinuousAt T x := contact_selection_continuousAt (continuous_cTransform hv) hv hT
    (fun y hy => contact_unique_of_mdifferentiable hv hDiff hy (hT x))
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hpI
  let q : V → V := fun h => κ (T (riemannianExp x h))
  have hq0 : q 0=p := by simp only [q,riemannianExp_zero,hTx,hκ0]
  have hTc' : ContinuousAt T (riemannianExp (n := n) x (0:V)) := by
    simpa only [riemannianExp_zero] using hTc
  have hcT : ContinuousAt (fun h : V => T (riemannianExp x h)) 0 :=
    hTc'.comp (contMDiff_riemannianExp_fiber x 0).continuousAt
  have hκ' : ContinuousAt κ (T (riemannianExp (n := n) x (0:V))) := by
    simpa only [riemannianExp_zero,hTx] using hκ.continuousAt
  have hqc : ContinuousAt q 0 := hκ'.comp (f := fun h : V => T (riemannianExp x h)) hcT
  have hqright : ∀ᶠ h in 𝓝 (0:V), riemannianExp x (q h)=T (riemannianExp x h) :=
    (show Tendsto (fun h : V => T (riemannianExp x h)) (𝓝 0) (𝓝 (riemannianExp x p)) from by
      simpa only [ContinuousAt,riemannianExp_zero,hTx] using hcT).eventually hκright
  obtain ⟨r,hr,K,hK,hconv⟩ := cTransform_uniform_smooth_coordinate_semiconvex
    (contMDiff_riemannianExp_fiber (n := n) x 0)
  let s : Set V := {h | h∈Metric.ball 0 r ∧ DifferentiableAt ℝ f h}
  let g : V → V := fun h => (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f h)
  have hg0 : g 0=p := by
    change (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f 0)=p
    rw [hexp.hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ V).symm_apply_apply p
  have hgD (h : V) (hh : h∈s) : HasFDerivAt f (innerSL ℝ (g h)) h := by
    apply hh.2.hasFDerivAt.congr_fderiv
    exact ((InnerProductSpace.toDual ℝ V).apply_symm_apply _).symm
  have hg := semiconvex_gradient_hasFDerivWithinAt hA hexp hr (K := 2*K)
    (by simpa only [mul_div_cancel_left₀ K (show (2:ℝ)≠0 by norm_num)] using hconv v hv)
  have hp1 : (1:ℝ) • p∈injectivityDomain x := by simpa only [one_smul] using hpI
  have hB := (prefixNormalCost_contDiffAt hp1).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnearB : ∀ᶠ h in 𝓝 (0:V), DifferentiableAt ℝ (prefixNormalCost x 1) (h,q h) := by
    have H := (hB.eventually (by norm_num)).mono
      (fun z hz => hz.differentiableAt (by norm_num))
    apply (continuousAt_id.prodMk hqc).tendsto.eventually
    simpa only [hq0,id_eq] using H
  refine ⟨r,hr,q,hq0,hqc,hqright,?_⟩
  apply twist_hasFDerivWithinAt hB
  · intro u w
    rw [prefixNormalCost_source_hessian_full hpI,inner_normalHessianOperator]
  · intro u w
    rw [hB.isSymmSndFDerivAt (by norm_num) |>.eq]
    simpa only [real_inner_comm] using (prefixNormalCost_hessian_blocks (show (0:ℝ)<1 by norm_num) hp1 w u).1
  · exact hq0
  · exact hqc
  · exact hg
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hqright,
      mem_nhdsWithin_of_mem_nhds hnearB] with h hh he hB'
    apply normal_contact_twist hv hB' _ (hgD h hh)
    rw [he]
    exact hT _
  · apply normal_contact_twist hv (hB.differentiableAt (by norm_num))
    · simpa only [riemannianExp_zero] using hp.2
    · change HasFDerivAt f (innerSL ℝ (g 0)) 0
      rw [hg0]
      exact hexp.hasFDerivAt

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI

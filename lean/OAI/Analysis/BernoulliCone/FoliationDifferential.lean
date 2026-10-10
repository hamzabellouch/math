import OAI.Analysis.BernoulliCone.UpperSmoothLeaves

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Spatial gradient of a smooth one-parameter family, as a joint field. -/
def spatialGradient (F:E×ℝ→ℝ) (p:E×ℝ) : E :=
  (toDual ℝ E).symm (fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ)

def divergence (V:E→E) (x:E) : ℝ :=
  ∑ i, inner ℝ (stdOrthonormalBasis ℝ E i) (fderiv ℝ V x (stdOrthonormalBasis ℝ E i))

lemma inner_spatialGradient (F:E×ℝ→ℝ) (p:E×ℝ) (v:E) :
    inner ℝ (spatialGradient F p) v = fderiv ℝ F p (v,0) := by
  rw [spatialGradient,←toDual_apply_apply (𝕜:=ℝ),LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma linear_prod_decomposition {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L:E×ℝ→L[ℝ] G) (v:E) (s:ℝ) : L (v,s)=L (v,0)+s • L (0,1) := by
  calc
    _ = L ((v,0)+s • ((0:E),(1:ℝ))) := by congr 1; ext <;> simp
    _ = _ := by rw [map_add,map_smul]

omit [FiniteDimensional ℝ E] in
lemma sliceLeft_hasFDerivAt {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F:E×ℝ→G} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    HasFDerivAt (fun x:E=>F (x,p.2)) (fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ) p.1 := by
  rcases p with ⟨x,t⟩
  have hi:HasFDerivAt (fun y:E=>(y,t)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
    simpa only [ContinuousLinearMap.inl,id_eq] using (hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const t x)
  exact hF.hasFDerivAt.comp x hi

lemma spatialGradient_eq {F:E×ℝ→ℝ} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    spatialGradient F p=gradient (fun x:E=>F (x,p.2)) p.1 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_spatialGradient,inner_gradient_left]
  have hd := sliceLeft_hasFDerivAt hF
  rw [hd.fderiv]
  simp

lemma spatialGradient_contDiffAt {F:E×ℝ→ℝ} {p:E×ℝ} (hF:ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (spatialGradient F) p := by
  have hpart : ContDiffAt ℝ ∞ (fun q:E×ℝ=>fderiv ℝ F q ∘L ContinuousLinearMap.inl ℝ E ℝ) p :=
    (hF.fderiv_right (by simp)).clm_comp contDiffAt_const
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp p hpart

lemma parameter_directional {F:E×ℝ→ℝ} {L:E×ℝ→ℝ} {p:E×ℝ}
    (hF:DifferentiableAt ℝ F (p.1,L p)) (hL:DifferentiableAt ℝ L p)
    (he:∀ᶠ z in 𝓝 p,F (z.1,L z)=z.2)
    (hρ:fderiv ℝ F (p.1,L p) (0,1)≠0) (v:E) (s:ℝ) :
    fderiv ℝ L p (v,s)=(s-inner ℝ (spatialGradient F (p.1,L p)) v)/
      fderiv ℝ F (p.1,L p) (0,1) := by
  have hd := hF.hasFDerivAt.comp p ((hasFDerivAt_fst (p:=p)).prodMk hL.hasFDerivAt)
  have hh := congrArg (fun T:E×ℝ→L[ℝ] ℝ=>T (v,s))
    ((hd.congr_of_eventuallyEq (he.mono (fun _ h=>h.symm))).unique (hasFDerivAt_snd (p:=p)))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ] at hh
  rw [linear_prod_decomposition,smul_eq_mul,←inner_spatialGradient] at hh
  change inner ℝ (spatialGradient F (p.1,L p)) v +
    fderiv ℝ L p (v,s) * fderiv ℝ F (p.1,L p) (0,1) = s at hh
  apply (eq_div_iff hρ).mpr
  linarith

lemma divergence_gradient {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ ∞ f x) :
    divergence (gradient f) x=Δ f x := by
  have hg:ContDiffAt ℝ ∞ (gradient f) x :=
    (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x (hf.fderiv_right (by simp))
  rw [divergence,laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  let v:=stdOrthonormalBasis ℝ E i
  have he:(fun y=>inner ℝ (gradient f y) v)=(fun y=>fderiv ℝ f y v) := by
    ext y
    exact inner_gradient_left
  have hh := congrArg (fun T:E→L[ℝ] ℝ=>T v) (congrArg (fun a:E→ℝ=>fderiv ℝ a x) he)
  have hdir: DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  rw [((hg.differentiableAt (by simp)).hasFDerivAt.inner ℝ (hasFDerivAt_const v x)).fderiv,
    fderiv_clm_apply hdir (differentiableAt_const v)] at hh
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,add_apply,ContinuousLinearMap.flip_apply,
    fderiv_const_apply,map_zero,zero_add] at hh
  simp only [fderivInnerCLM_apply,inner_zero_right,zero_add] at hh
  rw [real_inner_comm] at hh
  rw [iteratedFDeriv_two_apply]
  simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hh

/-- Cancellation of the parameter derivatives in the extended calibration.
This is the differential identity for an actual foliation, not an assumed PDE. -/
lemma foliation_divergence {F:E×ℝ→ℝ} {L:E×ℝ→ℝ} {p:E×ℝ}
    (hF:ContDiffAt ℝ ∞ F (p.1,L p)) (hL:ContDiffAt ℝ ∞ L p)
    (he:∀ᶠ z in 𝓝 p,F (z.1,L z)=z.2)
    (hρ:fderiv ℝ F (p.1,L p) (0,1)≠0) :
    let A:E×ℝ→E:=fun z=>spatialGradient F (z.1,L z)
    divergence (fun x=>A (x,p.2)) p.1+
      inner ℝ (A p) (deriv (fun t=>A (p.1,t)) p.2)=
      Δ (fun x:E=>F (x,L p)) p.1 := by
  dsimp only
  let q:E×ℝ:=(p.1,L p)
  let B:=spatialGradient F
  let A:E×ℝ→E:=fun z=>B (z.1,L z)
  let T:=fderiv ℝ B q (0,1)
  let ρ:=fderiv ℝ F q (0,1)
  have hBd:DifferentiableAt ℝ B q:=(spatialGradient_contDiffAt hF).differentiableAt (by simp)
  have hLd:DifferentiableAt ℝ L p:=hL.differentiableAt (by simp)
  have hFd:DifferentiableAt ℝ F q:=hF.differentiableAt (by simp)
  have hmap:HasFDerivAt (fun z:E×ℝ=>(z.1,L z))
      ((ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ L p)) p :=
    hasFDerivAt_fst.prodMk hLd.hasFDerivAt
  have hAd:HasFDerivAt A (fderiv ℝ B q ∘L
      ((ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ L p))) p :=
    by simpa only [A,Function.comp_def,q] using hBd.hasFDerivAt.comp p hmap
  have hd (v:E) (s:ℝ) : fderiv ℝ A p (v,s)=fderiv ℝ B q (v,0)+
      ((s-inner ℝ (B q) v)/ρ) • T := by
    rw [hAd.fderiv]
    change fderiv ℝ B q (v,fderiv ℝ L p (v,s)) = _
    rw [linear_prod_decomposition,parameter_directional hFd hLd he hρ]
  have hx (v:E) : fderiv ℝ (fun x:E=>A (x,p.2)) p.1 v=fderiv ℝ A p (v,0) := by
    rw [(sliceLeft_hasFDerivAt hAd.differentiableAt).fderiv]
    simp
  have ht : deriv (fun t:ℝ=>A (p.1,t)) p.2=ρ⁻¹ • T := by
    have hh:=hAd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    change HasDerivAt (fun t:ℝ=>A (p.1,t)) _ p.2 at hh
    rw [←hAd.fderiv] at hh
    rw [hh.deriv]
    rw [hd]
    simp only [inner_zero_right,sub_zero,one_div]
    rw [show ((0:E),(0:ℝ))=(0:E×ℝ) from rfl,map_zero,zero_add]
  have hspatial : divergence (fun x:E=>B (x,L p)) p.1=Δ (fun x:E=>F (x,L p)) p.1 := by
    have heq:(fun x:E=>B (x,L p)) =ᶠ[𝓝 p.1] gradient (fun x:E=>F (x,L p)) := by
      have hn:Tendsto (fun x:E=>(x,L p)) (𝓝 p.1) (𝓝 q):=continuousAt_id.prodMk continuousAt_const
      have hF1:ContDiffAt ℝ 1 F q:=hF.of_le (by simp)
      filter_upwards [hn.eventually (hF1.eventually (by simp))] with x hx
      exact spatialGradient_eq (hx.differentiableAt (by simp))
    have hfs:ContDiffAt ℝ ∞ (fun x:E=>F (x,L p)) p.1 :=
      hF.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
    rw [divergence,heq.fderiv_eq]
    exact divergence_gradient hfs
  have hbase (v:E):fderiv ℝ (fun x:E=>B (x,L p)) p.1 v=fderiv ℝ B q (v,0) := by
    rw [(sliceLeft_hasFDerivAt hBd).fderiv]
    simp
  change divergence (fun x=>A (x,p.2)) p.1+inner ℝ (B q) (deriv (fun t=>A (p.1,t)) p.2)=_
  rw [ht,←hspatial,divergence,divergence]
  simp_rw [hx,hbase,hd,inner_add_right,real_inner_smul_right,zero_sub,neg_div]
  rw [Finset.sum_add_distrib]
  have hec:(∑ i, -(inner ℝ (B q) (stdOrthonormalBasis ℝ E i)/ρ)*
      inner ℝ (stdOrthonormalBasis ℝ E i) T) = - (inner ℝ (B q) T/ρ) := by
    simp only [neg_mul,Finset.sum_neg_distrib,div_mul_eq_mul_div,←Finset.sum_div]
    rw [(stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  rw [hec]
  ring
end Bernoulli.Foliation

end
end

end OAI

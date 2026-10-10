import Mathlib
import OAI.Probability.LogConcave.Analysis.CompactGibbsIbp
import OAI.Probability.LogConcave.Sampling.MeanMaterialL2

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

def terminalMean (p : ℝ × Point d) : Point d :=
  conditionalFieldMean F x r (smoothTimeClip hT0 hT1 p.1)
    (terminalBackward hF x hr.le hl hT0 hT1 p)

lemma terminalMean_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalMean hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  let q : ℝ × Point d := (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)
  have hA := conditionalFieldMean_joint_smooth hF x hr.le (by linarith only [hl]) q
    (smoothTimeClip_sq_lt hT0 hT1 p.1)
  have hB : ContDiffAt ℝ (⊤:ℕ∞)
      (fun w : ℝ × Point d => (smoothTimeClip hT0 hT1 w.1,terminalBackward hF x hr.le hl hT0 hT1 w)) p :=
    ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1)).contDiffAt
  exact hA.comp p hB

lemma terminalBackward_deriv {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => terminalBackward hF x hr.le hl hT0 hT1 (t,y))
      (-r • conditionalFieldMean F x r ρ (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) ρ := by
  have he : smoothTimeClip hT0 hT1=ᶠ[nhds ρ] id := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with t ht
    exact smoothTimeClip_eq hT0 hT1 ⟨ht.1.le,ht.2.le⟩
  have hclip := (hasDerivAt_id ρ).congr_of_eventuallyEq he
  have hh := GlobalODE.flow_deriv (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr.le hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr.le hl hT0 hT1).continuous
    ⟨T,by constructor <;> linarith only [hT0]⟩ y ρ (by constructor <;> linarith)
  have hlow : (-1:ℝ)<ρ := by linarith only [hρ0]
  have hhigh : ρ<T+1 := by linarith only [hρT]
  have hflow := hh.hasDerivAt (Icc_mem_nhds hlow hhigh)
  have hs : smoothTimeClip hT0 hT1 ρ=ρ := he.eq_of_nhds
  rw [←hs] at hflow
  have hd := hflow.scomp ρ hclip
  simp only [hs,smoothProbabilityVelocity,probabilityVelocity,one_smul] at hd
  convert hd using 1 <;> first | rfl | simp only [terminalBackward,hs]

lemma terminalMean_direction {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (u y : Point d) :
    fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)=
      materialScalar F x r (fun t y => inner ℝ u (conditionalFieldMean F x r t y)) ρ
        (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) := by
  let A := fun p : ℝ × Point d => inner ℝ u (conditionalFieldMean F x r p.1 p.2)
  have hp : ρ^2<1 := by nlinarith [hρT.trans hT1]
  have ha : DifferentiableAt ℝ A (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) :=
    (contDiffAt_const.inner ℝ (conditionalFieldMean_joint_smooth hF x hr.le (by linarith only [hl]) (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) hp)).differentiableAt (by simp)
  have hd := ha.hasFDerivAt.comp_hasDerivAt ρ
    ((hasDerivAt_id ρ).prodMk (terminalBackward_deriv hF x hr hl hT0 hT1 hρ0 hρT y))
  have he : (fun t => inner ℝ u (terminalMean hF x hr hl hT0 hT1 (t,y)))=ᶠ[nhds ρ]
      (fun t => A (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))) := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with t ht
    simp only [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨ht.1.le,ht.2.le⟩,A]
  have hh := (((contDiff_const (c:=u)).inner ℝ (terminalMean_smooth hF x hr hl hT0 hT1)).differentiable (by simp) (ρ,y)).hasFDerivAt.comp_hasDerivAt ρ
    ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y))
  have hder : fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)=
      fderiv ℝ A (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))
        (1,-r • conditionalFieldMean F x r ρ (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) :=
    hh.unique (hd.congr_of_eventuallyEq he)
  rw [hder,joint_material_direction F x r ha]
  exact joint_mdir_eq_material F x r ha

lemma conditionalFieldMean_zero (y : Point d) :
    conditionalFieldMean F x r 0 y=∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r) := by
  unfold conditionalFieldMean
  have he : conditionalPotential F x r 0 y=primitivePotential F x r := by
    funext z
    simp [conditionalPotential,primitivePotential]
  rw [he]

lemma terminalMean_initial (y : Point d) :
    terminalMean hF x hr hl hT0 hT1 (0,y)=∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r) := by
  rw [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨le_rfl,hT0⟩,conditionalFieldMean_zero]

lemma terminalMean_final (y : Point d) :
    terminalMean hF x hr hl hT0 hT1 (T,y)=conditionalFieldMean F x r T y := by
  rw [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨hT0,le_rfl⟩,
    terminalBackward_eq hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩,probabilityTransport_initial]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter Function
open scoped NNReal RealInnerProductSpace Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hlam hl in
lemma conditionalFirstJet_symmetric_pos (hρ0 : 0<ρ) (hρ1 : ρ<1) (y : Point d) :
    (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)).IsSymmetric := by
  have hH := interpolationPotential_smooth hF x hr.le hl hρ0.le hρ1
  have he : gradient (interpolationPotential F x r ρ)=fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y :=
    funext (interpolationPotential_gradient hF x hr.le hl hρ0.le hρ1)
  have hd := (hasFDerivAt_id (𝕜:=ℝ) y).add
    (((conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1).differentiable (by simp) y).hasFDerivAt.const_smul (r*ρ))
  change HasFDerivAt (fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y) _ _ at hd
  have hh := ContDiff.isSymmetric_gradient_derivative (hH.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))) y
  rw [he,hd.fderiv,conditionalFirstJet_deriv hF x hr hlam hl hρ0.le hρ1 y] at hh
  intro u v
  have hs := hh u v
  change inner ℝ (u+(r*ρ) • (ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) u)) v=
    inner ℝ u (v+(r*ρ) • (ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v)) at hs
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,conj_trivial] at hs
  exact (mul_left_cancel₀ hρ0.ne')
    ((mul_left_cancel₀ (mul_ne_zero hr.ne' hρ0.ne')) (add_left_cancel hs))

include hF hr hlam hl in
lemma conditionalFirstJet_symmetric (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)).IsSymmetric := by
  rcases eq_or_lt_of_le hρ0 with h0|hpos
  · subst ρ
    intro u v
    have hc : ContinuousAt (fun t => conditionalFirstJet F x r ((lam:ℝ)*r) (t,y)) 0 :=
      (conditionalFirstJet_smooth hF x hr hlam hl (0,y) (by norm_num)).continuousAt.comp
        (f:=fun t : ℝ => (t,y)) (continuousAt_id.prodMk continuousAt_const)
    have h1 : Tendsto (fun t => inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) u) v) (nhds 0)
        (nhds (inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (0,y) u) v)) :=
      ((hc.clm_apply continuousAt_const).inner continuousAt_const).tendsto
    have h2 : Tendsto (fun t => inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) v)) (nhds 0)
        (nhds (inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (0,y) v))) :=
      (continuousAt_const.inner (hc.clm_apply continuousAt_const)).tendsto
    have e : (fun t => inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) u) v)=ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun t => inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) v)) := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ)<1 from by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      exact conditionalFirstJet_symmetric_pos hF x hr hlam hl ht ht1 y u v
    exact tendsto_nhds_unique (h1.mono_left nhdsWithin_le_nhds)
      ((h2.mono_left nhdsWithin_le_nhds).congr' e.symm)
  · exact conditionalFirstJet_symmetric_pos hF x hr hlam hl hpos hρ1 y
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalForward_slice_smooth (t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => terminalForward hF x hr.le hl hT0 hT1 (t,y)) :=
  (terminalForward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)

lemma terminalBackward_slice_smooth (t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => terminalBackward hF x hr.le hl hT0 hT1 (t,y)) :=
  (terminalBackward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)

def terminalHomeomorph (t : Icc (0:ℝ) T) : Point d ≃ₜ Point d where
  toFun := fun y => terminalForward hF x hr.le hl hT0 hT1 (t,y)
  invFun := fun y => terminalBackward hF x hr.le hl hT0 hT1 (t,y)
  left_inv := terminalBackward_forward hF x hr.le hl hT0 hT1 t
  right_inv := terminalForward_backward hF x hr.le hl hT0 hT1 t
  continuous_toFun := (terminalForward_slice_smooth hF x hr hl hT0 hT1 t).continuous
  continuous_invFun := (terminalBackward_slice_smooth hF x hr hl hT0 hT1 t).continuous

lemma terminal_integral_pushforward (t : Icc (0:ℝ) T) {f : Point d → ℝ} (hf : Continuous f) :
    (∫y,f y ∂interpolationLaw F x r T)=
      ∫z,f (terminalForward hF x hr.le hl hT0 hT1 (t,z)) ∂interpolationLaw F x r t := by
  rw [← probabilityTransport_pushforward hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩,
    integral_map (probabilityTransport_continuous hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩).measurable.aemeasurable hf.aestronglyMeasurable]
  simp only [terminalForward_eq]

include hF hr hlam hl hT1 in
lemma firstJet_pairing_sum (t : Icc (0:ℝ) T) (z u : Point d) (A : Point d →L[ℝ] ℝ) :
    (∑i : Fin d,conditionalU F x r t z u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()]*A (EuclideanSpace.basisFun (Fin d) ℝ i))=
      A (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he (i : Fin d) : conditionalU F x r t z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]=
      inner ℝ (b i) (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) := by
    rw [conditionalU_one_cov hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1),
      ←conditionalFirstJet_inner hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) u (b i) z]
    have hs := conditionalFirstJet_symmetric hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) z u (b i)
    change inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) (b i)=
      inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) (b i)) at hs
    exact hs.symm.trans (real_inner_comm _ _)
  change (∑i,conditionalU F x r t z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]*A (b i))=_
  simp only [he]
  have hh := congrArg A (b.sum_repr' (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u))
  simpa only [map_sum,map_smul,smul_eq_mul] using hh

include hlam in
lemma stein_pairing_integrand (t : Icc (0:ℝ) T) (z u : Point d)
    {φ : Point d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∑i : Fin d,conditionalU F x r t z u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()]*
        directional (EuclideanSpace.basisFun (Fin d) ℝ i)
          (fun y => φ (terminalForward hF x hr.le hl hT0 hT1 (t,y))) z)=
      fderiv ℝ φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))
        (steinIntegrand hF x hr hl hT0 hT1 (t,terminalForward hF x hr.le hl hT0 hT1 (t,z)) u) := by
  have hh := (hφ.differentiable (by norm_num) _).hasFDerivAt.comp z
    ((terminalForward_slice_smooth hF x hr hl hT0 hT1 t).differentiable (by simp) z).hasFDerivAt
  change HasFDerivAt (fun y => φ (terminalForward hF x hr.le hl hT0 hT1 (t,y))) _ _ at hh
  simp only [directional,hh.fderiv]
  rw [firstJet_pairing_sum hF x hr hlam hl hT1]
  simp only [steinIntegrand,smoothTimeClip_eq hT0 hT1 t.2,terminalBackward_forward,
    ContinuousLinearMap.comp_apply,terminalJacobian_eq]
  congr 2
  exact congrArg (fun f => fderiv ℝ f z) (funext (terminalForward_eq hF x hr.le hl hT0 hT1 t))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

lemma tensorAdjoint_continuous_C1 {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hV : ∀i,ContDiff ℝ 1 (V i)) (b : ι → Point d) :
    Continuous (tensorAdjoint H b V) := by
  apply continuous_finsetSum
  intro i _
  exact (((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
    (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam in
lemma stein_weak_derivative {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (u : Point d)
    {φ : Point d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)*φ y
      ∂interpolationLaw F x r T)=
      ∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (ρ,y) u) ∂interpolationLaw F x r T := by
  let t : Icc (0:ℝ) T := ⟨ρ,hρ0.le,hρT.le⟩
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let V := fun i : Fin d => fun z => conditionalU F x r ρ z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]
  let H := interpolationPotential F x r ρ
  have hp : ρ^2<1 := by nlinarith only [hρ0,hρT,hT1]
  have hV (i : Fin d) : ContDiff ℝ 1 (V i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact ((conditionalU_joint_smooth hF x hr hlam hl (fun _ : Unit => b i) [()] (by simp) u
      (ρ,z) hp).comp z (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  have hH : ContDiff ℝ 1 H := (interpolationPotential_smooth hF x hr.le hl hρ0.le (hρT.trans hT1)).of_le (by simp)
  have hAi : Integrable (fun z => Real.exp (-H z)) :=
    (interpolationPotential_lowerTail hF x hr.le (by linarith only [hl]) hρ0.le (hρT.trans hT1)).integrable_exp hH.continuous
  have hA := tensorAdjoint_continuous_C1 hH hV b
  have htest : ContDiff ℝ 1 (fun z => φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) :=
    hφ.comp ((terminalForward_slice_smooth hF x hr hl hT0 hT1 t).of_le (by simp))
  have htestc : HasCompactSupport (fun z => φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) :=
    hφc.comp_homeomorph (terminalHomeomorph hF x hr hl hT0 hT1 t)
  have hcR : Continuous (fun y => fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (t,y) u)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply
      (((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  simp_rw [terminalMean_direction hF x hr hl hT0 hT1 hρ0 hρT u,
    material_conditionalFieldMean hF x hr hlam hl hρ0.le (hρT.trans hT1)]
  change (∫y,tensorAdjoint H b V (terminalBackward hF x hr.le hl hT0 hT1 (t,y))*φ y ∂interpolationLaw F x r T)=_
  have hleft := terminal_integral_pushforward hF x hr hl hT0 hT1 t
    ((hA.comp (terminalBackward_slice_smooth hF x hr hl hT0 hT1 t).continuous).mul hφ.continuous)
  change (∫y,tensorAdjoint H b V (terminalBackward hF x hr.le hl hT0 hT1 (t,y))*φ y ∂interpolationLaw F x r T)=_ at hleft
  rw [hleft]
  have hright := terminal_integral_pushforward hF x hr hl hT0 hT1 t hcR
  change (∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (ρ,y) u) ∂interpolationLaw F x r T)=_ at hright
  rw [hright]
  simp only [Function.comp_def,Pi.mul_apply,terminalBackward_forward]
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl]) hp]
  change (∫z,tensorAdjoint H b V z*(φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) ∂gibbs H)=_
  rw [tensorAdjoint_compact_pairing hH hAi hV htest htestc b]
  apply integral_congr_ae
  filter_upwards [] with z
  exact stein_pairing_integrand hF x hr hlam hl hT0 hT1 t z u hφ
end LogConcaveSampling

end

end

end

end OAI

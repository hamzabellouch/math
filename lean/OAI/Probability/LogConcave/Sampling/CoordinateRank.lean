import Mathlib
import OAI.Probability.LogConcave.Sampling.TerminalBackward
import OAI.Probability.LogConcave.Numerics.ParametricFDeriv
import OAI.Probability.LogConcave.Sampling.JointU
import OAI.Probability.LogConcave.Sampling.ConditionalPositionMoment
import OAI.Probability.LogConcave.Sampling.JointConditionalLawProperties
import OAI.Probability.LogConcave.JetEstimates.JetNormalizedLaplaceMoments

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma conditionalU_moments_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup) (u y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) v l=
      ((1-ρ^2)^l.length)⁻¹*∑s∈l.toFinset.powerset,
        Appell.inverseMoment (fun t => conditionalPositionMoment F x r v t (ρ,y)) s*
          conditionalMixedMoment F x r u v (l.toFinset\s) (ρ,y) := by
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  rw [conditionalU_normalized_jet_sq hF x hr hlam hl hρ]
  rw [Appell.jet_normalizedLaplace_zero_moments
    (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y)
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le) v l hlN]
  rfl

theorem conditionalU_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup)
    (u : Point d) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalU F x r q.1 q.2 u ((lam:ℝ)*r) v l) p := by
  have hl' : (lam:ℝ)*r^2<1 := by linarith
  have hM (s : Finset ι) := conditionalPositionMoment_smooth hF x hr.le hl' v s p hp
  have hI (s : Finset ι) := Appell.inverseMoment_contDiffAt hM s
  have hX (s : Finset ι) := conditionalMixedMoment_smooth hF x hr.le hl' u v s p hp
  have hS : ContDiffAt ℝ (⊤:ℕ∞)
      (fun q => ∑s∈l.toFinset.powerset,
        Appell.inverseMoment (fun t => conditionalPositionMoment F x r v t q) s*
          conditionalMixedMoment F x r u v (l.toFinset\s) q) p :=
    ContDiffAt.sum (fun s _ => (hI s).mul (hX _))
  have hA : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => ((1-q.1^2)^l.length)⁻¹) p :=
    ((contDiffAt_const.sub (contDiffAt_fst.pow 2)).pow _).inv
      (pow_ne_zero _ (by linarith))
  apply (hA.mul hS).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditionalU_moments_sq hF x hr hlam hl hq v l hlN u q.2

lemma jointU_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup) (i : Fin d) :
    JetCalculus.TimeSmooth (jointU F x r ((lam:ℝ)*r) v l i) := by
  intro p h0 h1
  exact conditionalU_joint_smooth hF x hr hlam hl v l hlN _ p (by nlinarith)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped Topology NNReal RealInnerProductSpace

def coordinateRankOne (d : ℕ) (i j : Fin d) : Point d →L[ℝ] Point d :=
  (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)).smulRight
    (EuclideanSpace.basisFun (Fin d) ℝ i)

def conditionalFirstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  ∑i,∑j,conditionalU F x r p.1 p.2 (EuclideanSpace.basisFun (Fin d) ℝ i) L
    (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ j) [()] • coordinateRankOne d i j

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hF hr hlam hl in
lemma conditionalFirstJet_smooth (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalFirstJet F x r ((lam:ℝ)*r)) p := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (conditionalU_joint_smooth hF x hr hlam hl
    (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ j) [()] (by simp)
    (EuclideanSpace.basisFun (Fin d) ℝ i) p hp).smul contDiffAt_const

def terminalJacobian (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  (fderiv ℝ (terminalForward hF x hr.le hl hT0 hT1)
    (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Point d))

lemma terminalJacobian_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalJacobian hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (((terminalForward_smooth hF x hr.le hl hT0 hT1).fderiv_right (by simp)).comp
    ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1))).clm_comp contDiff_const

def steinIntegrand (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  (terminalJacobian hF x hr hl hT0 hT1 p).comp
    (conditionalFirstJet F x r ((lam:ℝ)*r)
      (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p))

include hlam in
lemma steinIntegrand_smooth : ContDiff ℝ (⊤:ℕ∞) (steinIntegrand hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  have hU : ContDiff ℝ (⊤:ℕ∞) (fun p => conditionalFirstJet F x r ((lam:ℝ)*r)
      (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (conditionalFirstJet_smooth hF x hr hlam hl _ (smoothTimeClip_sq_lt hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1)).contDiffAt
  exact (terminalJacobian_smooth hF x hr hl hT0 hT1).clm_comp hU

def centeringKernel (y : Point d) : Point d →L[ℝ] Point d :=
  (∫ρ in Icc 0 T,steinIntegrand hF x hr hl hT0 hT1 (ρ,y)).adjoint

include hlam in
lemma centeringKernel_smooth : ContDiff ℝ (⊤:ℕ∞) (centeringKernel hF x hr hl hT0 hT1) := by
  let : CompleteSpace (Point d →L[ℝ] Point d) := ContinuousLinearMap.instCompleteSpace
  have hs := CompactIntegral.smooth_parametric
    ((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).comp (contDiff_snd.prodMk contDiff_fst))
    (s:=Icc (0:ℝ) T) isCompact_Icc
  exact ContinuousLinearMap.adjoint.contDiff.comp hs
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma covariance_field_synthesis {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {f : Point d → ℝ} {g : Point d → Point d} (hf : MemLp f 2 μ)
    (hg : ∀u,MemLp (fun z => inner ℝ u (g z)) 2 μ) (v : Point d) :
    (∑i : Fin d,inner ℝ v ((EuclideanSpace.basisFun (Fin d) ℝ) i)*
      cov[f,(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) (g z));μ])=
      cov[f,(fun z => inner ℝ v (g z));μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hh := covariance_fun_sum_right
    (fun i : Fin d => (hg (b i)).const_mul (inner ℝ v (b i))) hf
  simp only [covariance_const_mul_right] at hh
  simpa only [b.sum_inner_mul_inner v] using hh.symm

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)

include hF hr hlam hl hρ0 hρ1 in
lemma conditionalFirstJet_inner (u v y : Point d) :
    inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v)=
      (1/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr.le hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr.le hl hρ0 hρ1 y
  have hi (v : Point d) : MemLp (fun z => inner ℝ v z) 2 μ :=
    (Appell.HasGrowth.linear (innerSL ℝ v)).memLp (by fun_prop) hm.hasMoments
  have hg (u : Point d) : MemLp (fun z => inner ℝ u (primitiveField F x r z)) 2 μ :=
    (primitiveField_inner_growth hF x u hr.le).memLp
      (continuous_const.inner (primitiveField_contDiff hF x r).continuous).aestronglyMeasurable hm.hasMoments
  simp only [conditionalFirstJet,sum_apply,smul_apply,
    inner_sum,inner_smul_right,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,conditionalU_one_cov hF x hr hlam hl hρ0 hρ1]
  change (∑i,∑j,(1/(1-ρ^2))*cov[(fun z => inner ℝ (b j) z),
    (fun z => inner ℝ (b i) (primitiveField F x r z));μ]*(inner ℝ (b j) v*inner ℝ u (b i)))=_
  calc
    _=(1/(1-ρ^2))*(∑i,inner ℝ u (b i)*(∑j,inner ℝ v (b j)*
        cov[(fun z => inner ℝ (b j) z),(fun z => inner ℝ (b i) (primitiveField F x r z));μ])) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) v]
      ring
    _=_ := by
      have hs (i : Fin d) := covariance_inner_synthesis hm (hg (b i)) v
      dsimp [μ,b] at hs ⊢
      simp only [hs]
      rw [covariance_field_synthesis (hi v) hg u]

include hF hr hlam hl hρ0 hρ1 in
lemma conditionalFirstJet_norm_le (y : Point d) :
    ‖conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)‖≤(Real.pi^2/2)*((lam:ℝ)*r) := by
  have ha := (probability_time hρ0 hρ1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let w := conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v
  have he := conditionalFirstJet_inner hF x hr hlam hl hρ0 hρ1 w v y
  have hb := mul_le_mul_of_nonneg_left
    (conditional_covariance_le hF x hr.le hl hρ0 hρ1 w v y) (by positivity : 0≤1/(1-ρ^2))
  have hh : ‖w‖^2≤((Real.pi^2/2)*((lam:ℝ)*r))*‖w‖*‖v‖ := by
    rw [←real_inner_self_eq_norm_sq w,he]
    calc
      _≤(1/(1-ρ^2))*|cov[(fun z => inner ℝ v z),
          (fun z => inner ℝ w (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _≤_ := by convert! hb using 1; field_simp [ha.ne']
  change ‖w‖≤_
  by_cases hw : ‖w‖=0
  · rw [hw]; positivity
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))).mp
    convert! hh using 1 <;> ring

include hF hr hlam hl hρ0 hρ1 in
lemma conditionalFirstJet_deriv (y : Point d) :
    fderiv ℝ (conditionalFieldMean F x r ρ) y=
      ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  simp only [smul_apply,inner_smul_right,
    conditionalFieldMean_inner_deriv hF x hr.le hl hρ0 hρ1,
    conditionalFirstJet_inner hF x hr hlam hl hρ0 hρ1]
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set Function
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalJacobian_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalJacobian hF x hr hl hT0 hT1 (t,y)=
      fderiv ℝ (probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩)
        (terminalBackward hF x hr.le hl hT0 hT1 (t,y)) := by
  have hh := ((terminalForward_smooth hF x hr.le hl hT0 hT1).differentiable (by simp)
    ((t:ℝ),terminalBackward hF x hr.le hl hT0 hT1 (t,y))).hasFDerivAt.comp
    (terminalBackward hF x hr.le hl hT0 hT1 (t,y))
    ((hasFDerivAt_const (t:ℝ) _).prodMk (hasFDerivAt_id _))
  have he : (fun z => terminalForward hF x hr.le hl hT0 hT1 (t,z))=
      probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩ :=
    funext (terminalForward_eq hF x hr.le hl hT0 hT1 t)
  change HasFDerivAt (fun z => terminalForward hF x hr.le hl hT0 hT1 (t,z)) _ _ at hh
  rw [he] at hh
  change HasFDerivAt _ ((fderiv ℝ (terminalForward hF x hr.le hl hT0 hT1)
    ((t:ℝ),terminalBackward hF x hr.le hl hT0 hT1 (t,y))).comp
      (ContinuousLinearMap.inr ℝ ℝ (Point d))) _ at hh
  simpa only [terminalJacobian,smoothTimeClip_eq hT0 hT1 t.2] using hh.fderiv.symm

lemma terminalJacobian_norm_le (t : Icc (0:ℝ) T) (y : Point d) :
    ‖terminalJacobian hF x hr hl hT0 hT1 (t,y)‖≤Real.exp (Real.pi^2/4) := by
  rw [terminalJacobian_eq]
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=terminalBackward hF x hr.le hl hT0 hT1 (t,y))
    (GlobalODE.flow_lipschitz
      (fun u (_ : u∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr.le hl hT0 hT1 u)
      (clampedProbabilityVelocity_continuous hF x hr.le hl hT0 hT1) t ⟨T,hT0,le_rfl⟩)
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have ht : 0≤T-(t:ℝ) := sub_nonneg.mpr t.2.2
  rw [abs_of_nonneg ht]
  have htt : T-(t:ℝ)≤1 := by linarith [t.2.1]
  have hbase : (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2/4 := by nlinarith [sq_nonneg Real.pi]
  exact (mul_le_of_le_one_right (by positivity : 0≤(Real.pi^2/2)*(lam:ℝ)*r^2) htt).trans hbase

include hlam in
lemma steinIntegrand_norm_le (t : Icc (0:ℝ) T) (y : Point d) :
    ‖steinIntegrand hF x hr hl hT0 hT1 (t,y)‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) := by
  unfold steinIntegrand
  calc
    _≤‖terminalJacobian hF x hr hl hT0 hT1 (t,y)‖*
      ‖conditionalFirstJet F x r ((lam:ℝ)*r)
        (smoothTimeClip hT0 hT1 t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _≤Real.exp (Real.pi^2/4)*((Real.pi^2/2)*((lam:ℝ)*r)) := by
      rw [smoothTimeClip_eq hT0 hT1 t.2]
      exact mul_le_mul (terminalJacobian_norm_le hF x hr hl hT0 hT1 t y)
        (conditionalFirstJet_norm_le hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) _)
        (norm_nonneg _) (Real.exp_pos _).le
    _=_ := by ring

include hlam in
theorem centeringKernel_norm_le (y : Point d) :
    ‖centeringKernel hF x hr hl hT0 hT1 y‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) := by
  unfold centeringKernel
  rw [ContinuousLinearMap.adjoint.norm_map]
  have hb := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (s:=Icc (0:ℝ) T) (f:=fun t => steinIntegrand hF x hr hl hT0 hT1 (t,y))
    isCompact_Icc.measure_lt_top
    (fun t ht => steinIntegrand_norm_le hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ y)
  apply hb.trans
  simp only [Measure.real,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT0]
  exact mul_le_of_le_one_right (by positivity) hT1.le
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators

lemma eq_zero_of_continuous_pos {f g : ℝ → ℝ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (he : ∀t,0<t → t<1 → f t=g t) : f 0=g 0 := by
  have hfg : f=ᶠ[nhdsWithin 0 (Set.Ioi 0)]g := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t h0 h1
    exact he t h0 h1
  exact tendsto_nhds_unique (hf.mono_left nhdsWithin_le_nhds)
    ((hg.mono_left nhdsWithin_le_nhds).congr' hfg.symm)

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]
lemma smooth_gadj_at (b : ι → E) {s V : ι → E → ℝ} {p : E}
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) p) :
    ContDiffAt ℝ (⊤:ℕ∞) (gadj b s V) p :=
  ContDiffAt.sum (fun i _ => smooth_cadj_at (b i) (hs i) (hV i))
end JetCalculus

lemma extra_list_nodup {ι : Type*} {l : List ι} (hl : l.Nodup) :
    (Sum.inr ()::l.map (Sum.inl (β:=Unit))).Nodup := by
  simp only [List.nodup_cons]
  refine ⟨?_,hl.map Sum.inl_injective⟩
  simp

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

theorem material_jointU {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => jointU F x r ((lam:ℝ)*r)
          (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::l.map Sum.inl) i) (ρ,y)+
      2*r*ρ*∑s∈l.toFinset.powerset.erase ∅,∑k,
        jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (ρ,y)*
          jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (ρ,y) := by
  let U := jointU F x r ((lam:ℝ)*r) v l i
  let V := fun k => jointU F x r ((lam:ℝ)*r)
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i
  let A := JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) U
  let B := fun p : ℝ × Point d => JetCalculus.gadj jointSpace (jointScore F x r) V p+
    2*r*p.1*∑s∈l.toFinset.powerset.erase ∅,∑k,
      jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k p*
        jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i p
  change A (ρ,y)=B (ρ,y)
  have hU := jointU_timeSmooth hF x hr hlam hl v l hlN i
  have hV (k : Fin d) := jointU_timeSmooth hF x hr hlam hl
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl)
      (extra_list_nodup hlN) i
  have hpos (t : ℝ) (h0 : 0<t) (h1 : t<1) : A (t,y)=B (t,y) := by
    have he := material_conditionalU_pos hF x hr hlam hl h0 h1 v l hlN i y
    have hs := JetCalculus.gadj_right_slice_at (JetCalculus.spaceBasis d) (jointScore F x r)
      (V:=V) (fun k => (hV k (t,y) (by dsimp; linarith) h1).differentiableAt (by simp))
    change JetCalculus.gadj jointSpace (jointScore F x r) V (t,y)=_ at hs
    change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (t,y)=_
    rw [he]
    exact congrArg (fun a => a+2*r*t*∑s∈l.toFinset.powerset.erase ∅,∑k,
      jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (t,y)*
        jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (t,y)) hs.symm
  rcases hρ0.eq_or_lt with hzero|hposρ
  · subst ρ
    have hz : (0:ℝ)^2<1 := by norm_num
    have hA : ContDiffAt ℝ (⊤:ℕ∞) A (0,y) :=
      JetCalculus.smooth_mdir_at (1,0) jointSpace r (jointMean_smooth_at hF x hr.le hl hz)
        (hU (0,y) (by norm_num) (by norm_num))
    have hB : ContDiffAt ℝ (⊤:ℕ∞) B (0,y) := by
      apply ContDiffAt.add
      · exact JetCalculus.smooth_gadj_at jointSpace (jointScore_smooth_at hF x hr.le hl hz)
          (fun k => hV k (0,y) (by norm_num) (by norm_num))
      · apply ContDiffAt.mul (contDiffAt_const.mul contDiffAt_fst)
        apply ContDiffAt.sum
        intro s _
        apply ContDiffAt.sum
        intro k _
        exact (jointU_timeSmooth hF x hr hlam hl v _ (hlN.filter _) k (0,y)
          (by norm_num) (by norm_num)).mul
          (jointU_timeSmooth hF x hr hlam hl _ _ (extra_list_nodup (hlN.filter _)) i (0,y)
            (by norm_num) (by norm_num))
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 :=
      continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (hA.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (hB.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc) hpos
  · exact hpos ρ hposρ hρ1

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_score_transport_nonneg {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace i) (jointMean F x r k)) (ρ,y) := by
  rcases hρ0.eq_or_lt with hz|hpos
  · subst ρ
    have hM := jointMean_smooth_at hF x hr.le hl (p:=(0,y)) (by norm_num)
    have hS := jointScore_smooth_at hF x hr.le hl (p:=(0,y)) (by norm_num)
    have ha := JetCalculus.smooth_mdir_at (1,0) jointSpace r hM (hS i)
    have hb := (contDiffAt_const (c:=r)).mul (JetCalculus.smooth_gadj_at jointSpace hS
      (fun k => JetCalculus.smooth_dir_at (hM k) (jointSpace i)))
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 := continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (ha.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (hb.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (fun t h0 h1 => joint_score_transport hF x hr hlam hl h0 h1 y i)
  · exact joint_score_transport hF x hr hlam hl hpos hρ1 y i

theorem physical_material_adjoint_nonneg {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {V : Fin d → ℝ × Point d → ℝ} {y : Point d}
    (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) (ρ,y)) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.gadj jointSpace (jointScore F x r) V) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun i => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V i)) (ρ,y)+
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y) := by
  have hp : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  exact JetCalculus.mdir_gadj_at _ _ _ (jointMean_smooth_at hF x hr.le hl hp)
    (jointScore_smooth_at hF x hr.le hl hp) hV (joint_score_transport_nonneg hF x hr hlam hl hρ0 hρ1 y)

end LogConcaveSampling

end

end

end

end OAI

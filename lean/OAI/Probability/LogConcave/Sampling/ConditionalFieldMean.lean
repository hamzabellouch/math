import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalMeanScalar
import OAI.Probability.LogConcave.JetEstimates.DirLogLaplace
import OAI.Probability.LogConcave.Sampling.JointPosition
import OAI.Probability.LogConcave.JetEstimates.MixedJetAdd

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace Topology

lemma primitiveField_inner_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x u : Point d) {r : ℝ} (hr : 0≤r) :
    Appell.HasGrowth (fun z => inner ℝ u (primitiveField F x r z)) :=
  Appell.HasGrowth.lipschitz ((innerSL ℝ u).lipschitzWith.comp (primitiveField_lipschitz hF x hr))

theorem conditionalFieldMean_logLaplace {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y h : Point d) :
    conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) (y+h)=
      ((lam:ℝ)*r)*JetCalculus.dir (jointField d u)
        (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
          (fun _ => (1:ℝ)) θ)) (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  rw [Appell.dir_log_laplace hm]
  change _=((lam:ℝ)*r)*Appell.normalizedLaplace
    ((gibbs (conditionalPotential F x r ρ y)).map (jointImage (primitiveField F x r) ((lam:ℝ)*r)))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d ((ρ/(1-ρ^2)) • h))
  rw [joint_normalizedLaplace (primitiveField_contDiff hF x r).continuous,
    ← mul_assoc,mul_inv_cancel₀ (by positivity : (lam:ℝ)*r≠0),one_mul]
  exact conditionalMeanScalar_shift hF x hr.le hl hρ0 hρ1 _ y h

theorem conditionalFieldMean_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) {ι : Type*} (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      ((lam:ℝ)*r)*(ρ/(1-ρ^2))^l.length*
        JetCalculus.jet (fun i => jointPosition d (v i)) l
          (JetCalculus.dir (jointField d u)
            (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
              (fun _ => (1:ℝ)) θ))) 0 := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  let f : JointPoint d → ℝ := fun θ => Real.log
    (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Appell.contDiff_laplace hm continuous_const (Appell.HasGrowth.const _)).log
      (fun θ => (Appell.laplace_one_pos hm θ).ne')
  have hds := JetCalculus.smooth_dir hfs (jointField d u)
  let B : Point d →L[ℝ] JointPoint d := (ρ/(1-ρ^2)) • jointPosition d
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun h => JetCalculus.dir (jointField d u) f (B h+0)) :=
    hds.comp (by fun_prop)
  have hs := conditionalMeanScalar_smooth hF x hr.le hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le)
  have htrans := congrFun (JetCalculus.jet_comp_affine hs (ContinuousLinearMap.id ℝ (Point d))
    y v l) 0
  have he : (fun h => conditionalMeanScalar F x r ρ
      (fun z => inner ℝ u (primitiveField F x r z)) (h+y))=
      fun h => ((lam:ℝ)*r)*JetCalculus.dir (jointField d u) f (B h+0) := by
    funext h
    simpa only [add_comm h y,B,smul_apply,map_smul,add_zero]
      using conditionalFieldMean_logLaplace hF x hr hlam hl hρ0 hρ1 u y h
  simp only [ContinuousLinearMap.id_apply,zero_add] at htrans
  rw [← htrans,he,JetCalculus.jet_const_mul hcomp,
    JetCalculus.jet_comp_affine hds B 0]
  simp only [map_zero,zero_add]
  have hB : (fun i => B (v i))=fun i => (ρ/(1-ρ^2)) • jointPosition d (v i) := rfl
  rw [hB,JetCalculus.jet_smul hds]
  ring

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma covariance_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (cov[f,g;μ])^2 ≤ Var[f;μ]*Var[g;μ] := by
  rw [covariance,variance_eq_integral hf.aemeasurable,variance_eq_integral hg.aemeasurable]
  exact integral_mul_sq_le (hf.sub (memLp_const _)) (hg.sub (memLp_const _))

namespace Appell
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma powerset_singleton {ι : Type*} [DecidableEq ι] (i : ι) :
    ({i}:Finset ι).powerset={∅,{i}} := by
  ext s
  simp [Finset.subset_singleton_iff]

lemma inverseMoment_singleton {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (i : ι) :
    inverseMoment m {i} = -m {i} := by
  rw [inverseMoment_nonempty _ (Finset.singleton_nonempty i).ne_empty]
  rw [powerset_singleton]
  simp

lemma polynomial_singleton {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (i : ι) (z : ι → ℝ) :
    polynomial m {i} z=z i-m {i} := by
  simp [polynomial, powerset_singleton, inverseMoment_singleton,sub_eq_add_neg]

lemma dir_normalizedLaplace_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {f : E → ℝ} (hf : Continuous f) (hg : HasGrowth f) (v : E) :
    JetCalculus.dir v (normalizedLaplace μ f) 0=
      cov[(fun z => inner ℝ v z),f;μ] := by
  have hh := jet_normalizedLaplace_zero hμ hf hg (fun _ : Unit => v) [()]
    (by simp)
  simp only [JetCalculus.jet,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,
    polynomial_singleton,moments,Finset.prod_singleton] at hh
  rw [hh]
  let g : E → ℝ := fun z => inner ℝ v z
  have hgm : MemLp g 2 μ := (HasGrowth.linear (innerSL ℝ v)).memLp
    (by fun_prop) hμ.hasMoments
  have hfm := hg.memLp hf.aestronglyMeasurable hμ.hasMoments
  rw [covariance_eq_sub hgm hfm]
  simp only [sub_mul]
  change (∫ x, g x*f x-(∫ z, g z ∂μ)*f x ∂μ)=_
  simpa only [Pi.mul_apply,integral_const_mul] using
    integral_sub (hgm.integrable_mul hfm)
      ((hfm.integrable (by norm_num)).const_mul (∫ z, g z ∂μ))

end Appell

theorem conditionalFieldMean_dir_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    JetCalculus.dir v
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
  let f : Point d → ℝ := fun z => inner ℝ u (primitiveField F x r z)
  have hfc : Continuous f := continuous_const.inner (primitiveField_contDiff hF x r).continuous
  have hfg : Appell.HasGrowth f := primitiveField_inner_growth hF x u hr
  have hmean := conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hfc hfg
  have hs := Appell.smooth_normalizedLaplace hm hfc hfg
  have he : (fun h => conditionalMeanScalar F x r ρ f (h+y))=
      fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h) := by
    funext h
    simpa only [add_comm h y] using conditionalMeanScalar_shift hF x hr hl hρ0 hρ1 f y h
  have htr := congrFun (JetCalculus.dir_comp_affine
    (hmean.differentiable (by simp)) (ContinuousLinearMap.id ℝ (Point d)) y v) 0
  simp only [ContinuousLinearMap.id_apply,zero_add] at htr
  rw [← htr,he]
  let B : Point d →L[ℝ] Point d := (ρ/(1-ρ^2)) • ContinuousLinearMap.id ℝ (Point d)
  have heB : (fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h))=
      fun h => Appell.normalizedLaplace μ f (B h+0) := by
    funext h; simp [B]
  rw [heB]
  rw [JetCalculus.dir_comp_affine (hs.differentiable (by simp))]
  simp only [map_zero,zero_add]
  change JetCalculus.dir ((ρ/(1-ρ^2)) • v) (Appell.normalizedLaplace μ f) 0=_
  rw [JetCalculus.dir_smul]
  change (ρ/(1-ρ^2))*JetCalculus.dir v (Appell.normalizedLaplace μ f) 0=_
  rw [Appell.dir_normalizedLaplace_zero hm hfc hfg]

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def conditionalFieldMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d := ∫ z, primitiveField F x r z ∂gibbs (conditionalPotential F x r ρ y)

lemma conditionalField_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (primitiveField F x r) (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact (Appell.HasGrowth.lipschitz (primitiveField_lipschitz hF x hr)).integrable
    (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

lemma conditionalFieldMean_inner {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u y : Point d) :
    inner ℝ u (conditionalFieldMean F x r ρ y)=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) y := by
  exact (integral_inner (conditionalField_integrable hF x hr hl hρ0 hρ1 y) u).symm

lemma conditionalFieldMean_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ContDiff ℝ (⊤ : ℕ∞) (conditionalFieldMean F x r ρ) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he : conditionalFieldMean F x r ρ = fun y => ∑ i : Fin d,
      conditionalMeanScalar F x r ρ (fun z => inner ℝ (b i) (primitiveField F x r z)) y • b i := by
    funext y
    simp_rw [← conditionalFieldMean_inner hF x hr hl hρ0 hρ1,
      ← b.repr_apply_apply]
    exact (b.sum_repr _).symm
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x (b i) hr)).smul contDiff_const

lemma conditional_covariance_le {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    |cov[(fun z => inner ℝ v z), (fun z => inner ℝ u (primitiveField F x r z));
      gibbs (conditionalPotential F x r ρ y)]| ≤
      ((Real.pi^2/2)*(1-ρ^2))*((lam:ℝ)*r)*‖u‖*‖v‖ := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  let f : Point d → ℝ := fun z => inner ℝ v z
  let g : Point d → ℝ := fun z => inner ℝ u (primitiveField F x r z)
  have hf : MemLp f 2 μ := (Appell.HasGrowth.linear (innerSL ℝ v)).memLp (by fun_prop) hm
  have hg : MemLp g 2 μ := (primitiveField_inner_growth hF x u hr).memLp
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous).aestronglyMeasurable hm
  have hP := conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y
  have hβ : 0≤(Real.pi^2/2)*(1-ρ^2) := mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le
  have hv := hP.lipschitz_variance hβ (innerSL ℝ v).contDiff (innerSL ℝ v).lipschitzWith hf
  have hu := hP.lipschitz_variance hβ ((innerSL ℝ u).contDiff.comp (primitiveField_contDiff hF x r))
    ((innerSL ℝ u).lipschitzWith.comp (primitiveField_lipschitz hF x hr)) hg
  simp only [NNReal.coe_mul,coe_nnnorm,innerSL_apply_norm,NNReal.coe_mk] at hv hu
  change Var[f;μ] ≤ _ at hv
  change Var[g;μ] ≤ _ at hu
  have hb := (covariance_sq_le hf hg).trans
    (mul_le_mul hv hu (variance_nonneg g μ) (mul_nonneg hβ (sq_nonneg _)))
  change |cov[f,g;μ]| ≤ _
  have hh : 0≤((Real.pi^2/2)*(1-ρ^2))*((lam:ℝ)*r)*‖u‖*‖v‖ := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hh).mp
  rw [sq_abs]
  convert! hb using 1
  ring

lemma conditionalFieldMean_inner_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    inner ℝ u (fderiv ℝ (conditionalFieldMean F x r ρ) y v)=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z), (fun z => inner ℝ u (primitiveField F x r z));
        gibbs (conditionalPotential F x r ρ y)] := by
  have he : (fun y => inner ℝ u (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr hl hρ0 hρ1 u)
  have hd := (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).differentiable (by simp)
  have hh := (innerSL ℝ u).hasFDerivAt.comp y (hd y).hasFDerivAt
  have hh' := congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh.fderiv
  change JetCalculus.dir v (fun y => inner ℝ u (conditionalFieldMean F x r ρ y)) y=
    inner ℝ u (fderiv ℝ (conditionalFieldMean F x r ρ) y v) at hh'
  rw [←hh',he]
  exact conditionalFieldMean_dir_cov hF x hr hl hρ0 hρ1 u v y

theorem conditionalFieldMean_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith ⟨(Real.pi^2/2)*ρ*((lam:ℝ)*r), by positivity⟩
      (conditionalFieldMean F x r ρ) := by
  have hd := (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).differentiable (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le hd
  intro y
  apply (show ‖fderiv ℝ (conditionalFieldMean F x r ρ) y‖ ≤ (Real.pi^2/2)*ρ*((lam:ℝ)*r) from ?_)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let w := fderiv ℝ (conditionalFieldMean F x r ρ) y v
  have he := conditionalFieldMean_inner_deriv hF x hr hl hρ0 hρ1 w v y
  have hb := mul_le_mul_of_nonneg_left (conditional_covariance_le hF x hr hl hρ0 hρ1 w v y)
    (div_nonneg hρ0 (probability_time hρ0 hρ1).1.le)
  have hh : ‖w‖^2 ≤ ((Real.pi^2/2)*ρ*((lam:ℝ)*r))*‖w‖*‖v‖ := by
    rw [←real_inner_self_eq_norm_sq w,he]
    calc
      _ ≤ (ρ/(1-ρ^2))*|cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ w (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (div_nonneg hρ0 (probability_time hρ0 hρ1).1.le)
      _ ≤ _ := by
        convert! hb using 1
        field_simp [(probability_time hρ0 hρ1).1.ne']
  change ‖w‖ ≤ _
  by_cases hw : ‖w‖=0
  · rw [hw]; positivity
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))).mp
    convert! hh using 1 <;> ring

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def quadraticTilt {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (p : Point d × ℝ) : E :=
  ∫ z, Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) • h z

def quadraticLinear {d : ℕ} (z : Point d) : (Point d × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ z).comp (ContinuousLinearMap.fst ℝ (Point d) ℝ) -
    ‖z‖^2 • ContinuousLinearMap.snd ℝ (Point d) ℝ

def quadraticDerivative {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : Point d → E) (z : Point d) : (Point d × ℝ) →L[ℝ] E :=
  (quadraticLinear z).smulRight (h z)

lemma quadraticLinear_apply {d : ℕ} (z : Point d) (p : Point d × ℝ) :
    quadraticLinear z p=inner ℝ p.1 z-p.2*‖z‖^2 := by
  simp [quadraticLinear,real_inner_comm,mul_comm]

lemma continuous_quadraticLinear {d : ℕ} : Continuous (quadraticLinear (d:=d)) := by
  exact ((innerSL ℝ).continuous.clm_comp continuous_const).sub
    ((continuous_norm.pow 2).smul continuous_const)

lemma norm_quadraticLinear {d : ℕ} (z : Point d) :
    ‖quadraticLinear z‖  ≤  ‖z‖+‖z‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [quadraticLinear_apply]
  calc
    ‖inner ℝ p.1 z-p.2*‖z‖^2‖  ≤  ‖p.1‖*‖z‖+‖p.2‖*‖z‖^2 := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (by simp [norm_mul]))
    _  ≤  ‖p‖*‖z‖+‖p‖*‖z‖^2 := add_le_add
      (mul_le_mul_of_nonneg_right (norm_fst_le p) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_snd_le p) (sq_nonneg _))
    _ = (‖z‖+‖z‖^2)*‖p‖ := by ring

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_quadraticDerivative {h : Point d → E} (hh : Continuous h) :
    Continuous (quadraticDerivative h) :=
  isBoundedBilinearMap_smulRight.continuous.comp (continuous_quadraticLinear.prodMk hh)

lemma growth_quadraticDerivative {h : Point d → E} (hg : HasPolynomialGrowth h) :
    HasPolynomialGrowth (quadraticDerivative h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨4*C,by positivity,n+2,fun z => ?_⟩
  have hz := norm_nonneg z
  have hb : ‖quadraticDerivative h z‖  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := by
    rw [quadraticDerivative,ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (norm_quadraticLinear z) (hn z) (norm_nonneg _) (by positivity)
  by_cases h1 : ‖z‖ ≤ 1
  · have hp : ‖z‖^n ≤ 1 := pow_le_one₀ hz h1
    have h2 : ‖z‖^2 ≤ 1 := pow_le_one₀ hz h1
    calc
      _  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := hb
      _  ≤  2*(C*2) := mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hC)
        (by positivity) (by norm_num)
      _  ≤  _ := by nlinarith [mul_nonneg hC (pow_nonneg hz (n+2))]
  · have h1' : 1 ≤ ‖z‖ := le_of_not_ge h1
    have he (k : ℕ) (hk : k ≤ n+2) : ‖z‖^k ≤ ‖z‖^(n+2) := pow_le_pow_right₀ h1' hk
    have hA := he 1 (by omega)
    have hB := he 2 (by omega)
    have hD := he (n+1) (by omega)
    simp only [pow_one] at hA
    calc
      _  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := hb
      _ = C*(‖z‖+‖z‖^2+‖z‖^(n+1)+‖z‖^(n+2)) := by
        simp only [pow_add,pow_one]; ring
      _  ≤  C*(4*‖z‖^(n+2)) := mul_le_mul_of_nonneg_left (by linarith) hC
      _  ≤  _ := by nlinarith

lemma integrable_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    Integrable (fun z => Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) • h z) := by
  have ht' : HasGaussianLowerTail (fun z => H z+p.2*‖z‖^2) :=
    ⟨m+p.2,hp,C,fun z => by nlinarith [ht z]⟩
  convert! integrable_tilted _ (hH.add (continuous_const.mul (continuous_norm.pow 2))) hh ht' hg p.1 using 1
  funext z; congr 2; dsimp; ring

lemma hasFDerivAt_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    HasFDerivAt (quadraticTilt H h) (quadraticTilt H (quadraticDerivative h) p) p := by
  let δ := (m+p.2)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let M := ‖p.1‖+1
  obtain ⟨K,hK,n,hg'⟩ := growth_quadraticDerivative hg
  let B := Real.exp (C+M^2/(2*δ))*K
  let b : Point d → ℝ := fun z => B*(Real.exp (-(δ/2)*‖z‖^2)+‖z‖^n*Real.exp (-(δ/2)*‖z‖^2))
  have hi : Integrable b := ((integrable_gaussian_envelope d (b:=δ/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b:=δ/2) (by positivity))).const_mul B
  let U : Set (Point d × ℝ) := {q | ‖q.1‖ < M ∧ p.2-δ < q.2}
  have hopen : IsOpen U := (isOpen_lt (continuous_fst.norm) continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hU : U∈nhds p := by
    apply hopen.mem_nhds
    change ‖p.1‖ < M ∧ p.2-δ < p.2
    exact ⟨by dsimp [M]; linarith,by linarith⟩
  have hd (z : Point d) (q : Point d × ℝ) :
      HasFDerivAt (fun t => Real.exp (inner ℝ t.1 z-t.2*‖z‖^2-H z) • h z)
        (Real.exp (inner ℝ q.1 z-q.2*‖z‖^2-H z) • quadraticDerivative h z) q := by
    have hh' := (((quadraticLinear z).hasFDerivAt (x:=q)).sub_const (H z)).exp.smul_const (h z)
    convert! hh' using 1
    · funext t; rw [quadraticLinear_apply]
    · apply ContinuousLinearMap.ext; intro t
      simp [quadraticDerivative,quadraticLinear_apply,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F':=fun q z => Real.exp (inner ℝ q.1 z-q.2*‖z‖^2-H z) • quadraticDerivative h z)
    (bound:=b) hU
  · exact Filter.Eventually.of_forall fun q =>
      ((Real.continuous_exp.comp (((continuous_const.inner continuous_id).sub
        (continuous_const.mul (continuous_norm.pow 2))).sub hH)).smul hh).aestronglyMeasurable
  · exact integrable_quadraticTilt hH hh ht hg p hp
  · exact (integrable_quadraticTilt hH (continuous_quadraticDerivative hh) ht
      (growth_quadraticDerivative hg) p hp).aestronglyMeasurable
  · filter_upwards [] with z q hq
    have ht' : ∀ z, δ*‖z‖^2 ≤ (H z+q.2*‖z‖^2)+C := by
      intro z
      have hq' : δ ≤ m+q.2 := by dsimp [U,δ] at *; linarith [hq.2]
      nlinarith [ht z,mul_nonneg (sub_nonneg.mpr hq') (sq_nonneg ‖z‖)]
    have he := mul_le_mul (gaussian_tilt_bound hδ (by dsimp [M]; positivity) ht' hq.1.le z)
      (hg' z) (norm_nonneg _) (by positivity)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    convert! he using 1
    · congr 2; ring
    · dsimp [b,B]; ring
  · exact hi
  · exact Filter.Eventually.of_forall fun z q _ => hd z q

theorem contDiffAt_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (quadraticTilt H h) p := by
  apply contDiffAt_infty.mpr
  intro n
  induction n generalizing E h with
  | zero =>
    apply contDiffAt_zero.mpr
    refine ⟨{q | 0 < m+q.2},?_,fun q hq =>
      (hasFDerivAt_quadraticTilt hH hh ht hg q hq).continuousAt.continuousWithinAt⟩
    exact (isOpen_lt continuous_const (continuous_const.add continuous_snd)).mem_nhds hp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨quadraticTilt H (quadraticDerivative h),?_,ih
      (continuous_quadraticDerivative hh) (growth_quadraticDerivative hg)⟩
    refine ⟨{q | 0 < m+q.2},?_,fun q hq => hasFDerivAt_quadraticTilt hH hh ht hg q hq⟩
    exact (isOpen_lt continuous_const (continuous_const.add continuous_snd)).mem_nhds hp

end
end LogConcaveSampling

end UpperProof
end
end
end

end OAI

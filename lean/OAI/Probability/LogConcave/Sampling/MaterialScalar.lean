import Mathlib
import OAI.Probability.LogConcave.Analysis.InterpolationPotential
import OAI.Probability.LogConcave.Sampling.ConditionalSlotEmbedding
import OAI.Probability.LogConcave.JetEstimates.PolyC1

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal RealInnerProductSpace

lemma quadraticTilt_derivative_apply {d : ℕ} {H h : Point d → ℝ}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀z,m*‖z‖^2≤H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m + p.2) (v : Point d × ℝ) :
    quadraticTilt H (quadraticDerivative h) p v=
      quadraticTilt H (fun z => quadraticLinear z v*h z) p := by
  unfold quadraticTilt
  rw [ContinuousLinearMap.integral_apply (integrable_quadraticTilt hH
    (continuous_quadraticDerivative hh) ht (growth_quadraticDerivative hg) p hp)]
  rfl

theorem fderiv_quadraticExpectation {d : ℕ} {H h : Point d → ℝ}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀z,m*‖z‖^2≤H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m + p.2) (v : Point d × ℝ) :
    fderiv ℝ (quadraticExpectation H h) p v=
      quadraticExpectation H (fun z => quadraticLinear z v*h z) p-
      quadraticExpectation H (fun z => quadraticLinear z v) p*quadraticExpectation H h p := by
  have h1 := hasFDerivAt_quadraticTilt hH continuous_const ht (growth_const (1:ℝ)) p hp
  have hh' := hasFDerivAt_quadraticTilt hH hh ht hg p hp
  have hZ := (quadratic_partition_pos hH ht p hp).ne'
  have hq := ((hasDerivAt_inv hZ).comp_hasFDerivAt p h1).mul hh'
  change HasFDerivAt (quadraticExpectation H h) _ p at hq
  rw [hq.fderiv]
  simp only [add_apply,smul_apply,Function.comp_apply,
    smul_eq_mul,quadraticTilt_derivative_apply hH hh ht hg p hp,
    quadraticTilt_derivative_apply hH continuous_const ht (growth_const (1:ℝ)) p hp,mul_one,
    quadraticExpectation]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal RealInnerProductSpace

lemma hasDerivAt_conditionalParameter_time {d : ℕ} (y : Point d) {ρ : ℝ} (hρ : ρ^2<1) :
    HasDerivAt (fun t => conditionalParameter (t,y))
      (((1+ρ^2)/(1-ρ^2)^2) • y,ρ/(1-ρ^2)^2) ρ := by
  have ha : 1-ρ^2≠0 := by linarith
  have hi := hasDerivAt_id ρ
  have hd := (hasDerivAt_const ρ (1:ℝ)).sub (hi.pow 2)
  have hA := (hi.div hd ha).smul_const y
  have hB := (hi.pow 2).div (hd.const_mul 2) (mul_ne_zero (by norm_num) ha)
  convert hA.prodMk hB using 1
  · rfl
  · apply Prod.ext
    · dsimp
      congr 1
      field_simp
      ring
    · dsimp
      field_simp
      ring

theorem deriv_conditional_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) (y : Point d)
    {h : Point d → ℝ} (hh : Continuous h) (hg : HasPolynomialGrowth h) :
    deriv (fun t => ∫z,h z ∂gibbs (conditionalPotential F x r t y)) ρ=
      (∫z,(((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2)*h z
        ∂gibbs (conditionalPotential F x r ρ y))-
      (∫z,((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2
        ∂gibbs (conditionalPotential F x r ρ y))*(∫z,h z ∂gibbs (conditionalPotential F x r ρ y)) := by
  let H := primitivePotential F x r
  let p := conditionalParameter (ρ,y)
  let q := (((1+ρ^2)/(1-ρ^2)^2) • y,ρ/(1-ρ^2)^2)
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hH : Continuous H := hF.continuous_potential x r
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  have hqe := (contDiffAt_quadraticExpectation hH hh ht hg p hp).differentiableAt (by simp)
  have he : (fun t => ∫z,h z ∂gibbs (conditionalPotential F x r t y))=ᶠ[nhds ρ]
      (fun t => quadraticExpectation H h (conditionalParameter (t,y))) := by
    have hb : ∀ᶠt in nhds ρ,t^2<1 := (isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hρ
    filter_upwards [hb] with t ht
    exact conditional_integral_quadratic hF x hr hl ht y h
  have hd := hqe.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_conditionalParameter_time y hρ)
  have hd' := hd.congr_of_eventuallyEq he
  rw [hd'.deriv]
  change fderiv ℝ (quadraticExpectation H h) p q=_
  rw [fderiv_quadraticExpectation hH hh ht hg p hp q]
  have hq (z : Point d) : quadraticLinear z q=
      ((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2 := by
    simp only [quadraticLinear_apply,q,inner_smul_left,starRingEnd_apply,star_trivial]
  simp_rw [hq]
  rw [←conditional_integral_quadratic hF x hr hl hρ y,
    ←conditional_integral_quadratic hF x hr hl hρ y,
    ←conditional_integral_quadratic hF x hr hl hρ y]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal RealInnerProductSpace

theorem conditionalIntegral_dir_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (v y : Point d) {f : Point d → ℝ}
    (hfc : Continuous f) (hfg : Appell.HasGrowth f) :
    JetCalculus.dir v
      (conditionalMeanScalar F x r ρ f) y=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        f;gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
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

theorem conditionalU_one_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u v y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) (fun _ : Unit => v) [()]=
      (1/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  obtain ⟨hp,hm,hP⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  have hL : (lam:ℝ)*r≠0 := by positivity
  simp only [conditionalU,List.length_singleton,pow_one,JetCalculus.jet]
  rw [Appell.dir_log_laplace hm]
  have hg : Appell.HasGrowth (fun z : JointPoint d => inner ℝ (jointField d u) z) :=
    Appell.HasGrowth.linear (innerSL ℝ (jointField d u))
  rw [Appell.dir_normalizedLaplace_zero hm (by fun_prop) hg]
  unfold jointConditionalLaw
  rw [covariance_map_fun (by fun_prop) (by fun_prop)
    ((jointImage_contDiff (primitiveField_contDiff hF x r) _).continuous.aemeasurable)]
  simp only [jointPosition_inner,jointField_inner,covariance_const_mul_right]
  field_simp

lemma conditional_observable_memLp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {f : Point d → ℝ} (hf : Continuous f) (hg : Appell.HasGrowth f) :
    MemLp f 2 (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact hg.memLp hf.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

lemma conditional_covariance_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) :
    (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)])=
      fun y => conditionalMeanScalar F x r ρ (fun z => g z*h z) y-
        conditionalMeanScalar F x r ρ g y*conditionalMeanScalar F x r ρ h y := by
  funext y
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact covariance_eq_sub (conditional_observable_memLp hF x hr hl hρ0 hρ1 y gc gg)
    (conditional_observable_memLp hF x hr hl hρ0 hρ1 y hc hg)

lemma conditional_covariance_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)]) := by
  rw [conditional_covariance_eq hF x hr hl hρ0 hρ1 gc gg hc hg]
  exact (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 (gc.mul hc) (gg.mul hg)).sub
    ((conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 gc gg).mul
      (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hc hg))

lemma directional_conditional_covariance {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) (v y : Point d) :
    directional v (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)]) y=
      (ρ/(1-ρ^2))*(cov[(fun z => inner ℝ v z),(fun z => g z*h z);
          gibbs (conditionalPotential F x r ρ y)]-
        cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]*
          conditionalMeanScalar F x r ρ h y-
        conditionalMeanScalar F x r ρ g y*
          cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)]) := by
  rw [conditional_covariance_eq hF x hr hl hρ0 hρ1 gc gg hc hg]
  have hgd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 gc gg).differentiable (by simp)
  have hhd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hc hg).differentiable (by simp)
  have hpd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 (gc.mul hc) (gg.mul hg)).differentiable (by simp)
  simp only [directional]
  change (fderiv ℝ (conditionalMeanScalar F x r ρ (g*h)-
    conditionalMeanScalar F x r ρ g*conditionalMeanScalar F x r ρ h) y) v=_
  rw [((hpd y).hasFDerivAt.sub ((hgd y).hasFDerivAt.mul (hhd y).hasFDerivAt)).fderiv]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  change JetCalculus.dir v _ y-(conditionalMeanScalar F x r ρ g y*JetCalculus.dir v _ y+
    conditionalMeanScalar F x r ρ h y*JetCalculus.dir v _ y)=_
  rw [conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y (gc.mul hc) (gg.mul hg),
    conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y hc hg,
    conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y gc gg]
  change (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),g*h;gibbs (conditionalPotential F x r ρ y)]-
    (conditionalMeanScalar F x r ρ g y*((ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)])+
    conditionalMeanScalar F x r ρ h y*((ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]))=
    (ρ/(1-ρ^2))*(cov[(fun z => inner ℝ v z),g*h;gibbs (conditionalPotential F x r ρ y)]-
    cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]*conditionalMeanScalar F x r ρ h y-
    conditionalMeanScalar F x r ρ g y*cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)])
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma covariance_third_diagonal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g h : Ω → ℝ} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hgg : MemLp (fun z => (g z)^2) 2 μ) (hgh : MemLp (fun z => g z*h z) 2 μ) :
    cov[g,(fun z => g z*h z);μ]-cov[g,g;μ]*(∫z,h z ∂μ)-
      (∫z,g z ∂μ)*cov[g,h;μ]=
      cov[(fun z => (g z)^2),h;μ]-2*(∫z,g z ∂μ)*cov[g,h;μ] := by
  rw [covariance_eq_sub hg hgh,covariance_eq_sub hg hg,
    covariance_eq_sub hg hh,covariance_eq_sub hgg hh]
  simp only [Pi.mul_apply,pow_two,←mul_assoc]
  ring

lemma covariance_inner_synthesis {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hm : Appell.HasExpMoments μ) {f : Point d → ℝ} (hf : MemLp f 2 μ) (v : Point d) :
    (∑i : Fin d,inner ℝ v ((EuclideanSpace.basisFun (Fin d) ℝ) i)*
      cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),f;μ])=
      cov[(fun z => inner ℝ v z),f;μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi (i : Fin d) : MemLp (fun z => inner ℝ (b i) z) 2 μ :=
    (Appell.HasGrowth.linear (innerSL ℝ (b i))).memLp (by fun_prop) hm.hasMoments
  have hh := covariance_fun_sum_left (fun i => (hi i).const_mul (inner ℝ v (b i))) hf
  simp only [covariance_const_mul_left] at hh
  simpa only [b.sum_inner_mul_inner v] using hh.symm

lemma covariance_norm_sq_sum {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hm : Appell.HasExpMoments μ) {f : Point d → ℝ} (hf : MemLp f 2 μ) :
    (∑i : Fin d,cov[(fun z => (inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z)^2),f;μ])=
      cov[(fun z => ‖z‖^2),f;μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi (i : Fin d) : MemLp (fun z => (inner ℝ (b i) z)^2) 2 μ :=
    ((Appell.HasGrowth.linear (innerSL ℝ (b i))).pow 2).memLp (by fun_prop) hm.hasMoments
  have hh := covariance_fun_sum_left hi hf
  simpa only [b.sum_sq_inner_right] using hh.symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

def materialScalar {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (A : ℝ → Point d → ℝ) (ρ : ℝ) (y : Point d) : ℝ :=
  deriv (fun t => A t y) ρ-r*directional (conditionalFieldMean F x r ρ y) (A ρ) y

lemma deriv_conditional_integral_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) :
    deriv (fun t => conditionalMeanScalar F x r t f y) ρ=
      ((1+ρ^2)/(1-ρ^2)^2)*cov[(fun z => inner ℝ y z),f;gibbs (conditionalPotential F x r ρ y)]-
      (ρ/(1-ρ^2)^2)*cov[(fun z => ‖z‖^2),f;gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg : Appell.HasGrowth (fun z : Point d => inner ℝ y z) := Appell.HasGrowth.linear (innerSL ℝ y)
  have hn : Appell.HasGrowth (fun z : Point d => ‖z‖^2) := by
    exact ⟨1,by norm_num,2,fun z => by simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z‖)]; linarith⟩
  have gm : MemLp (fun z : Point d => inner ℝ y z) 2 μ := hg.memLp (by fun_prop) hm
  have nm : MemLp (fun z : Point d => ‖z‖^2) 2 μ := hn.memLp (by fun_prop) hm
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm
  let A := (1+ρ^2)/(1-ρ^2)^2
  let B := ρ/(1-ρ^2)^2
  have qm : MemLp (fun z : Point d => A*inner ℝ y z-B*‖z‖^2) 2 μ :=
    (gm.const_mul A).sub (nm.const_mul B)
  change deriv (fun t => ∫z,f z ∂gibbs (conditionalPotential F x r t y)) ρ=_
  rw [deriv_conditional_integral hF x hr (by linarith)
    (by have := (probability_time hρ0 hρ1).1; linarith) y fc fg]
  have hq := covariance_eq_sub qm fm
  simp only [Pi.mul_apply] at hq
  rw [←hq,covariance_fun_sub_left (gm.const_mul A) (nm.const_mul B) fm]
  simp only [covariance_const_mul_left,A,B]
  rfl

lemma directional_position_covariance {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (v y : Point d)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) :
    directional v (fun y => cov[(fun z => inner ℝ v z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      (ρ/(1-ρ^2))*(cov[(fun z => (inner ℝ v z)^2),f;gibbs (conditionalPotential F x r ρ y)]-
        2*conditionalMeanScalar F x r ρ (fun z => inner ℝ v z) y*
          cov[(fun z => inner ℝ v z),f;gibbs (conditionalPotential F x r ρ y)]) := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg : Appell.HasGrowth (fun z : Point d => inner ℝ v z) := Appell.HasGrowth.linear (innerSL ℝ v)
  have gm : MemLp (fun z : Point d => inner ℝ v z) 2 μ := hg.memLp (by fun_prop) hm
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm
  rw [directional_conditional_covariance hF x hr hl hρ0 hρ1 (by fun_prop) hg fc fg]
  exact congrArg (fun z => (ρ/(1-ρ^2))*z) (covariance_third_diagonal gm fm ((hg.pow 2).memLp (by fun_prop) hm)
    ((hg.mul fg).memLp ((show Continuous (fun z => inner ℝ v z) by fun_prop).mul fc).aestronglyMeasurable hm))

theorem material_conditional_expectation {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) (y : Point d) :
    materialScalar F x r (fun t => conditionalMeanScalar F x r t f) ρ y=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i y => (1/(1-ρ^2))*cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),f;
          gibbs (conditionalPotential F x r ρ y)]) y := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm.hasMoments
  let a := 1-ρ^2
  have ha : a≠0 := (probability_time hρ0 hρ1).1.ne'
  let M := conditionalFieldMean F x r ρ y
  let C (v : Point d) := cov[(fun z => inner ℝ v z),f;μ]
  let S (i : Fin d) := cov[(fun z => (inner ℝ (b i) z)^2),f;μ]
  let m (i : Fin d) := conditionalMeanScalar F x r ρ (fun z => inner ℝ (b i) z) y
  let w := y+(r*ρ) • M
  have hi (i : Fin d) : Appell.HasGrowth (fun z : Point d => inner ℝ (b i) z) :=
    Appell.HasGrowth.linear (innerSL ℝ (b i))
  have hD (i : Fin d) : directional (b i)
      (fun y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      (1/a)*(ρ/a)*(S i-2*m i*C (b i)) := by
    have hdc := (conditional_covariance_smooth hF x hr hl hρ0 hρ1 (by fun_prop) (hi i) fc fg).differentiable (by simp)
    change JetCalculus.dir (b i) (fun y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=_
    rw [JetCalculus.dir_const_mul hdc]
    change (1/a)*directional (b i) (fun y => cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=_
    rw [directional_position_covariance hF x hr hl hρ0 hρ1 (b i) y fc fg]
    dsimp [S,m,C,μ,a]
    ring
  have hme (i : Fin d) : m i=ρ*inner ℝ y (b i)-(a*r)*inner ℝ M (b i) := by
    dsimp [m,conditionalMeanScalar]
    rw [integral_inner (conditional_identity_integrable hF x hr hl hρ0 hρ1 y) (b i),
      conditional_mean_identity hF x hr hl hρ0 hρ1 y]
    simp only [inner_sub_right,inner_smul_right]
    rw [real_inner_comm (b i) y,real_inner_comm (b i) M]
  have hsum (v : Point d) : (∑i : Fin d,inner ℝ v (b i)*C (b i))=C v :=
    covariance_inner_synthesis hm fm v
  have hmSum : (∑i : Fin d,m i*C (b i))=ρ*C y-(a*r)*C M := by
    simp only [hme,sub_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum,hsum]
  have hsSum : (∑i : Fin d,S i)=cov[(fun z => ‖z‖^2),f;μ] := covariance_norm_sq_sum hm fm
  have hwSum : (∑i : Fin d,inner ℝ w (b i)*C (b i))=C y+(r*ρ)*C M := by
    simp only [w,inner_add_left,real_inner_smul_left,add_mul,mul_assoc,
      Finset.sum_add_distrib,←Finset.mul_sum,hsum]
  rw [materialScalar,deriv_conditional_integral_cov hF x hr hl hρ0 hρ1 y fc fg]
  change _-r*JetCalculus.dir M (conditionalMeanScalar F x r ρ f) y=_
  rw [conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 M y fc fg]
  have hAdj : tensorAdjoint (interpolationPotential F x r ρ) b
      (fun i y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      -((1/a)*(ρ/a))*cov[(fun z => ‖z‖^2),f;μ]+
        (2*(1/a)*(ρ/a))*(ρ*C y-(a*r)*C M)+(1/a)*(C y+(r*ρ)*C M) := by
    unfold tensorAdjoint adjointCoordinate
    simp only [hD,directional_gradient,interpolationPotential_gradient hF x hr hl hρ0 hρ1]
    calc
      _=(∑i : Fin d,(-((1/a)*(ρ/a))*S i+
          (2*(1/a)*(ρ/a))*(m i*C (b i))+(1/a)*(inner ℝ w (b i)*C (b i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        change -((1/a)*(ρ/a)*(S i-2*m i*C (b i)))+inner ℝ w (b i)*((1/a)*C (b i))=_
        ring
      _=_ := by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum,hsSum,hmSum,hwSum]
  rw [hAdj]
  change ((1+ρ^2)/a^2)*C y-(ρ/a^2)*cov[(fun z => ‖z‖^2),f;μ]-r*((ρ/a)*C M)=_
  dsimp [a]
  field_simp [show 1-ρ^2≠0 from ha]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal RealInnerProductSpace

lemma conditionalLaw_probability_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ : ρ^2<1) (y : Point d) :
    IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) := by
  have ha : 0<1-ρ^2 := by linarith
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0≤r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  rw [← conditionalLaw_map hF x r ρ y ha]
  infer_instance

lemma conditionalLaw_hasExpMoments_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ : ρ^2<1) (y : Point d) :
    Appell.HasExpMoments (gibbs (conditionalPotential F x r ρ y)) := by
  have ha : 0<1-ρ^2 := by linarith
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0≤r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  rw [← conditionalLaw_map hF x r ρ y ha]
  apply (hF.hasExpMoments (x+r • (ρ • y)) hrad hsmall).map_lipschitz
    (K := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

lemma conditionalFieldMean_inner_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) (u y : Point d) :
    inner ℝ u (conditionalFieldMean F x r ρ y)=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) y := by
  let := conditionalLaw_probability_sq hF x hr hl hρ y
  have hi : Integrable (primitiveField F x r) (gibbs (conditionalPotential F x r ρ y)) :=
    (Appell.HasGrowth.lipschitz (primitiveField_lipschitz hF x hr)).integrable
      (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable
      (conditionalLaw_hasExpMoments_sq hF x hr hl hρ y).hasMoments
  exact (integral_inner hi u).symm

theorem material_conditionalFieldMean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) :
    materialScalar F x r (fun t y => inner ℝ u (conditionalFieldMean F x r t y)) ρ y=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
          (fun _ : Unit => (EuclideanSpace.basisFun (Fin d) ℝ) i) [()]) y := by
  have hρ : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have he : (fun t => inner ℝ u (conditionalFieldMean F x r t y))=ᶠ[nhds ρ]
      (fun t => conditionalMeanScalar F x r t (fun z => inner ℝ u (primitiveField F x r z)) y) := by
    filter_upwards [(isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hρ] with t ht
    exact conditionalFieldMean_inner_sq hF x hr.le hl ht u y
  have hs : (fun y => inner ℝ u (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 u)
  have hu : (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
      (fun _ : Unit => (EuclideanSpace.basisFun (Fin d) ℝ) i) [()])=
      (fun i y => (1/(1-ρ^2))*cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]) :=
    funext fun i => funext fun y => conditionalU_one_cov hF x hr hlam hl hρ0 hρ1 u _ y
  rw [hu]
  unfold materialScalar
  rw [he.deriv_eq]
  dsimp only
  rw [hs]
  exact material_conditional_expectation hF x hr.le hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le) y

end LogConcaveSampling

end

end

end

end OAI

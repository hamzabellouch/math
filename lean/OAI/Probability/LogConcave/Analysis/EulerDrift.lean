import Mathlib
import OAI.Probability.LogConcave.Sampling.PolynomialGrowth

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open MeasureTheory Filter
open scoped RealInnerProductSpace NNReal ENNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}

theorem Primitive.contDiff_potential (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    ContDiff ℝ 2 (primitivePotential F x r) :=
  ((contDiff_norm_sq ℝ).div_const 2).add
    (hF.smooth.comp (contDiff_const.add (contDiff_id.const_smul r)))

theorem Primitive.gradient_potential (hF : Primitive F lam) (x : Point d) (r : ℝ)
    (z : Point d) : gradient (primitivePotential F x r) z = z+r • gradient F (x+r • z) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha : HasFDerivAt (fun w : Point d => x+r • w)
      (0+r • ContinuousLinearMap.id ℝ (Point d)) z :=
    (hasFDerivAt_const x z).add ((hasFDerivAt_id z).const_smul r)
  have hb := (hF.smooth.differentiable (by norm_num) (x+r • z)).hasFDerivAt.comp z ha
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_smul (1/2 : ℝ)).add hb
  convert! hd using 1
  · funext w
    simp only [primitivePotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul]
    ring
  ext v
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,zero_add,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    inner_add_left,real_inner_smul_left,innerSL_apply_apply,
    map_smul,← toDual_gradient]
  ring

theorem Primitive.gradient_potential_lipschitz (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (1+lam*(NNReal.mk r hr)^2) (gradient (primitivePotential F x r)) := by
  have hh := LipschitzWith.id.add (modeStep_lipschitz hF.gradient_lipschitz x hr).neg
  convert! hh using 1
  funext z
  simp only [hF.gradient_potential,Pi.neg_apply,modeStep,neg_smul,neg_neg,id_eq]

theorem Primitive.gaussianLowerTail (hF : Primitive F lam) (x : Point d) {r : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2 < 1) : HasGaussianLowerTail (primitivePotential F x r) := by
  let m := 1-(lam:ℝ)*r^2
  let a := r*‖gradient F x‖
  have hm : 0 < m := sub_pos.mpr hl
  refine ⟨m/4,by positivity,a^2/m-F x,fun z => ?_⟩
  have hb := quadratic_remainder_of_gradient_lipschitz hF.smooth hF.gradient_lipschitz x (r • z)
  rw [abs_le] at hb
  have hc := abs_real_inner_le_norm (r • z) (gradient F x)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hb hc
  have hy := sq_nonneg (m*‖z‖-2*a)
  have hdiv : a^2/m*m=a^2 := div_mul_cancel₀ _ hm.ne'
  have hin : -a*‖z‖ ≤ inner ℝ (r • z) (gradient F x) := by
    have hh := neg_abs_le (inner ℝ (r • z) (gradient F x))
    dsimp [a]
    nlinarith only [hc,hh]
  dsimp only [primitivePotential]
  dsimp [m] at *
  nlinarith [mul_nonneg (show 0 ≤ 1-(lam:ℝ)*r^2 by linarith) (sq_nonneg ‖z‖)]

lemma partition_pos_of_continuous {H : Point d → ℝ} (hc : Continuous H) : 0 < partition H := by
  have hm : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [partition,lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity H) = Set.univ := by
    ext z
    simp [Function.mem_support,gibbsDensity,not_le_of_gt (Real.exp_pos (-H z))]
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

lemma partition_ne_top_of_integrable {H : Point d → ℝ}
    (hi : Integrable (fun z => Real.exp (-H z))) : partition H ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (Real.exp_pos (-H z)).le)).2 hi

lemma probability_gibbs_of_partition {H : Point d → ℝ}
    (hp : partition H ≠ 0) (ht : partition H ≠ ⊤) : IsProbabilityMeasure (gibbs H) := by
  constructor
  rw [gibbs,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hp ht

lemma lipschitz_sq_norm_growth {g : Point d → Point d} {M : ℝ≥0} (hg : LipschitzWith M g) :
    HasPolynomialGrowth (fun z => ‖g z‖^2) := by
  refine ⟨2*((M:ℝ)^2+‖g 0‖^2),by positivity,2,fun z => ?_⟩
  have hb : ‖g z‖ ≤ (M:ℝ)*‖z‖+‖g 0‖ := by
    have hh := hg.dist_le_mul z 0
    rw [dist_eq_norm,dist_zero_right] at hh
    linarith only [norm_le_norm_sub_add (g z) (g 0),hh]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hp := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith [sq_nonneg ((M:ℝ)*‖z‖-‖g 0‖),mul_nonneg (sq_nonneg ‖g 0‖) (sq_nonneg ‖z‖)]

theorem Primitive.gradient_sq_integrable (hF : Primitive F lam) (x : Point d) {r : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2 < 1) :
    Integrable (fun z => ‖gradient (primitivePotential F x r) z‖^2)
      (gibbs (primitivePotential F x r)) := by
  have hg := hF.gradient_potential_lipschitz x hr
  apply integrable_gibbs_of_weighted (hF.continuous_potential x r)
    (hF.integrable_exp_neg_potential x hr hl)
  have hh := integrable_tilted (primitivePotential F x r)
    (hF.continuous_potential x r) (hg.continuous.norm.pow 2)
    (hF.gaussianLowerTail x hr hl) (lipschitz_sq_norm_growth hg) 0
  simpa only [inner_zero_left,zero_sub,smul_eq_mul,Pi.pow_apply] using hh

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

def eulerDrift {d : ℕ} (H : Point d → ℝ) (h : ℝ) (z : Point d) : Point d :=
  z-h • gradient H z

lemma Primitive.eulerDrift_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r h : ℝ) (z : Point d) :
    eulerDrift (primitivePotential F x r) h z =
      (1-h) • z+h • modeStep (gradient F) x r z := by
  rw [eulerDrift,hF.gradient_potential]
  dsimp [modeStep]
  module

lemma Primitive.eulerDrift_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    LipschitzWith ⟨1-h+h*((lam:ℝ)*r^2),by positivity⟩
      (eulerDrift (primitivePotential F x r) h) := by
  have hl := modeStep_lipschitz hF.gradient_lipschitz x hr
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [hF.eulerDrift_eq]
  have hb := dist_add_add_le ((1-h) • z) (h • modeStep (gradient F) x r z)
    ((1-h) • w) (h • modeStep (gradient F) x r w)
  simp only [dist_smul₀, Real.norm_eq_abs,abs_of_nonneg hh,
    abs_of_nonneg (sub_nonneg.mpr hh1)] at hb
  have hd := hl.dist_le_mul z w
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk] at hd
  change _ ≤ (1-h+h*((lam:ℝ)*r^2))*dist z w
  nlinarith only [hb,mul_le_mul_of_nonneg_left hd hh]

lemma Primitive.contDiff_eulerDrift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r h : ℝ) :
    ContDiff ℝ 1 (eulerDrift (primitivePotential F x r) h) := by
  have hg : ContDiff ℝ 1 (gradient F) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.smooth.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp hd
  have he : eulerDrift (primitivePotential F x r) h = fun z =>
      (1-h) • z+h • (-r • gradient F (x+r • z)) := by
    funext z
    exact hF.eulerDrift_eq x r h z
  rw [he]
  exact (contDiff_id.const_smul (1-h)).add
    (((hg.comp (contDiff_const.add (contDiff_id.const_smul r))).const_smul (-r)).const_smul h)

end LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace GaussianPoincare
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rotation (θ : ℝ) : E × E →L[ℝ] E × E :=
  ((Real.cos θ • ContinuousLinearMap.fst ℝ E E) +
    (Real.sin θ • ContinuousLinearMap.snd ℝ E E)).prod
  ((-Real.sin θ • ContinuousLinearMap.fst ℝ E E) +
    (Real.cos θ • ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rotation_apply (θ : ℝ) (x y : E) :
    rotation θ (x,y) = (Real.cos θ • x+Real.sin θ • y,
      -Real.sin θ • x+Real.cos θ • y) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_energy (θ : ℝ) (x y : E) :
    ‖Real.cos θ • x+Real.sin θ • y‖^2+
      ‖-Real.sin θ • x+Real.cos θ • y‖^2 = ‖x‖^2+‖y‖^2 := by
  simp only [norm_add_sq_real,real_inner_smul_left,real_inner_smul_right,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_gaussian (θ : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map (rotation θ) =
      (stdGaussian E).prod (stdGaussian E) := by
  apply Measure.ext_of_charFunDual
  ext L
  let L₁ := L.comp (ContinuousLinearMap.inl ℝ E E)
  let L₂ := L.comp (ContinuousLinearMap.inr ℝ E E)
  have h₁ : (L.comp (rotation θ)).comp (ContinuousLinearMap.inl ℝ E E) =
      Real.cos θ • L₁ + (-Real.sin θ) • L₂ := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      rotation_apply,smul_zero,add_zero]
    change L (Real.cos θ • x,-Real.sin θ • x) = _
    have hp : (Real.cos θ • x,-Real.sin θ • x) =
        Real.cos θ • (x,0) + (-Real.sin θ) • (0,x) := by simp
    rw [hp,L.map_add,L.map_smul,L.map_smul]
    rfl
  have h₂ : (L.comp (rotation θ)).comp (ContinuousLinearMap.inr ℝ E E) =
      Real.sin θ • L₁ + Real.cos θ • L₂ := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      rotation_apply,smul_zero,zero_add]
    change L (Real.sin θ • x,Real.cos θ • x) = _
    have hp : (Real.sin θ • x,Real.cos θ • x) =
        Real.sin θ • (x,0) + Real.cos θ • (0,x) := by simp
    rw [hp,L.map_add,L.map_smul,L.map_smul]
    rfl
  rw [charFunDual_map,charFunDual_prod,h₁,h₂,charFunDual_prod]
  simp only [charFunDual_stdGaussian]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  have he := rotation_energy (-θ) ((InnerProductSpace.toDual ℝ E).symm L₁)
    ((InnerProductSpace.toDual ℝ E).symm L₂)
  simp only [← map_smul,← map_add,LinearIsometryEquiv.norm_map] at he
  simp only [Real.cos_neg,Real.sin_neg,neg_neg] at he
  norm_cast
  dsimp [L₁,L₂] at *
  linarith

lemma integral_dual_sq (L : StrongDual ℝ E) :
    ∫ x, (L x)^2 ∂stdGaussian E = ‖L‖^2 := by
  have hm : MemLp L 2 (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp L
  have hv := variance_dual_stdGaussian L
  rw [variance_eq_sub hm,integral_strongDual_stdGaussian,zero_pow (by norm_num),sub_zero] at hv
  exact hv

lemma interval_integral_sq_le {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) : (∫ t in 0..T, f t)^2 ≤ T*∫ t in 0..T, (f t)^2 := by
  let j := ∫ t in 0..T, f t
  have hi := hf.intervalIntegrable (μ := volume) 0 T
  have hi2 : IntervalIntegrable (fun t => (f t)^2) volume 0 T :=
    (hf.pow 2).intervalIntegrable (μ := volume) 0 T
  have hp : 0 ≤ ∫ t in 0..T, (T*f t-j)^2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  have he : (fun t => (T*f t-j)^2) =
      fun t => T^2*(f t)^2-2*T*j*f t+j^2 := by funext t; ring_nf
  have hs : IntervalIntegrable (fun t => T^2*(f t)^2-2*T*j*f t) volume 0 T :=
    (hi2.const_mul _).sub (hi.const_mul _)
  rw [he,intervalIntegral.integral_add hs (intervalIntegrable_const),
    intervalIntegral.integral_sub (hi2.const_mul _) (hi.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hp
  dsimp [j] at *
  simp only [sub_zero] at hp
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_first_deriv (θ : ℝ) (x y : E) : HasDerivAt
    (fun t => (rotation t (x,y)).1) ((rotation θ (x,y)).2) θ := by
  convert! ((Real.hasDerivAt_cos θ).smul_const x).add
    ((Real.hasDerivAt_sin θ).smul_const y) using 1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma along_rotation_deriv {h : E → ℝ} (hh : ContDiff ℝ 1 h) (x y : E) (θ : ℝ) :
    HasDerivAt (fun t => h ((rotation t (x,y)).1))
      (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)) θ :=
  (hh.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ
    (rotation_first_deriv θ x y)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_difference_bound {h : E → ℝ} (hh : ContDiff ℝ 1 h) (x y : E) :
    (h y-h x)^2 ≤ (Real.pi/2)*∫ θ in 0..Real.pi/2,
      (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2))^2 := by
  have hc : Continuous (fun θ =>
      fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)) := by
    have hd := hh.continuous_fderiv (by norm_num)
    exact (hd.comp (by simp only [rotation_apply]; fun_prop)).clm_apply
      (by simp only [rotation_apply]; fun_prop)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => along_rotation_deriv hh x y θ) (hc.intervalIntegrable 0 (Real.pi/2))
  simp only [rotation_apply,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,
    add_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,zero_add] at he
  rw [← he]
  exact interval_integral_sq_le (by positivity) hc

lemma memLp_lipschitz {h : E → ℝ} {K : ℝ≥0} (hl : LipschitzWith K h) :
    MemLp h 2 (stdGaussian E) := by
  have hl₀ : LipschitzWith K (fun x => h x-h 0) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simpa using hl.dist_le_mul x y)
  have hm := hl₀.comp_memLp (by simp) (IsGaussian.memLp_two_id (μ := stdGaussian E))
  have hp : MemLp (fun x => h x-h 0+h 0) 2 (stdGaussian E) :=
    hm.add (memLp_const (h 0))
  simpa only [sub_add_cancel] using hp

lemma independent_difference_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hm : MemLp h 2 μ) :
    ∫ xy, (h xy.1-h xy.2)^2 ∂μ.prod μ = 2*Var[h;μ] := by
  have hi := hm.integrable (by norm_num)
  have hi2 := hm.integrable_sq
  have hc := hi.mul_prod hi
  have he : (fun xy : Ω × Ω => (h xy.1-h xy.2)^2) =
      fun xy => (h xy.1)^2-2*(h xy.1*h xy.2)+(h xy.2)^2 := by
    funext xy; ring_nf
  have hs : Integrable (fun xy : Ω × Ω => (h xy.1)^2-2*(h xy.1*h xy.2))
      (μ.prod μ) := (hi2.comp_fst μ).sub (hc.const_mul 2)
  rw [he,integral_add hs (hi2.comp_snd μ),
    integral_sub (hi2.comp_fst μ) (hc.const_mul 2),integral_const_mul,
    integral_fun_fst (μ := μ) (ν := μ) (fun x => h x^2),
    integral_fun_snd (μ := μ) (ν := μ) (fun x => h x^2),
    integral_prod_mul,variance_eq_sub hm]
  simp only [probReal_univ,one_smul,Pi.pow_apply]
  ring_nf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma tangent_sq_bound {h : E → ℝ} {K : ℝ≥0} (hl : LipschitzWith K h)
    (θ : ℝ) (x y : E) :
    (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2))^2 ≤
      2*(K:ℝ)^2*(‖x‖^2+‖y‖^2) := by
  have hD := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := (rotation θ (x,y)).1)
  have h₁ := (fderiv ℝ h ((rotation θ (x,y)).1)).le_opNorm ((rotation θ (x,y)).2)
  have h₂ : ‖(rotation θ (x,y)).2‖ ≤ ‖x‖+‖y‖ := by
    simp only [rotation_apply]
    calc
      ‖-Real.sin θ • x+Real.cos θ • y‖ ≤ ‖-Real.sin θ • x‖+‖Real.cos θ • y‖ := norm_add_le _ _
      _ ≤ ‖x‖+‖y‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_neg]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg x) (Real.abs_sin_le_one θ))
          (mul_le_of_le_one_left (norm_nonneg y) (Real.abs_cos_le_one θ))
  have hb : ‖fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)‖ ≤
      (K:ℝ)*(‖x‖+‖y‖) := h₁.trans ((mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h₂ K.coe_nonneg))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
  nlinarith [mul_nonneg (sq_nonneg (K:ℝ)) (sq_nonneg (‖x‖-‖y‖))]

lemma unrotated_integrable {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) :
    Integrable (fun xy : E × E => (fderiv ℝ h xy.1 xy.2)^2)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hn : Integrable (fun y : E => ‖y‖^2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  refine ((hn.comp_snd (stdGaussian E)).const_mul ((K:ℝ)^2)).mono'
    (by exact ((hh.continuous_fderiv (by norm_num)).comp continuous_fst |>.clm_apply
      continuous_snd |>.pow 2).aestronglyMeasurable) ?_
  filter_upwards [] with xy
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := (fderiv ℝ h xy.1).le_opNorm xy.2
  have hc := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := xy.1)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hb.trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))) 2
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow] using hs

lemma integral_tangent_sq {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) (θ : ℝ) :
    ∫ xy : E × E, (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2
      ∂(stdGaussian E).prod (stdGaussian E) =
    ∫ x, ‖fderiv ℝ h x‖^2 ∂stdGaussian E := by
  have hc : Continuous (fun xy : E × E => (fderiv ℝ h xy.1 xy.2)^2) :=
    ((hh.continuous_fderiv (by norm_num)).comp continuous_fst |>.clm_apply continuous_snd).pow 2
  rw [← integral_map (rotation θ).continuous.aemeasurable hc.aestronglyMeasurable,
    rotation_gaussian,integral_prod _ (unrotated_integrable hh hl)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integral_dual_sq (fderiv ℝ h x))

lemma tangent_time_integrable {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) (T : ℝ) :
    Integrable (fun p : ℝ × (E × E) =>
      (fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2)
      ((volume.restrict (Set.uIoc 0 T)).prod
        ((stdGaussian E).prod (stdGaussian E))) := by
  have hn : Integrable (fun y : E => ‖y‖^2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  let : IsFiniteMeasure (volume.restrict (Set.uIoc 0 T)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  have hb := ((hn.comp_fst (stdGaussian E)).add
    (hn.comp_snd (stdGaussian E))).const_mul (2*(K:ℝ)^2)
  refine (hb.comp_snd (volume.restrict (Set.uIoc 0 T))).mono' ?_ ?_
  · have hc : Continuous (fun p : ℝ × (E × E) =>
        (fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2) := by
      refine Continuous.pow (Continuous.clm_apply
        ((hh.continuous_fderiv (by norm_num)).comp ?_) ?_) 2
      · change Continuous (fun p : ℝ × (E × E) => Real.cos p.1 • p.2.1 +
          Real.sin p.1 • p.2.2)
        fun_prop
      · change Continuous (fun p : ℝ × (E × E) => -Real.sin p.1 • p.2.1 +
          Real.cos p.1 • p.2.2)
        fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    change ‖(fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2‖ ≤
      2*(K:ℝ)^2*(‖p.2.1‖^2+‖p.2.2‖^2)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact tangent_sq_bound hl p.1 p.2.1 p.2.2

theorem variance_le_gradient {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) :
    Var[h;stdGaussian E] ≤ (Real.pi^2/8)*
      ∫ x, ‖fderiv ℝ h x‖^2 ∂stdGaussian E := by
  let μ := (stdGaussian E).prod (stdGaussian E)
  let T := Real.pi/2
  have hT : 0 < T := by dsimp [T]; positivity
  have hi := tangent_time_integrable hh hl T
  have hinner : Integrable (fun xy : E × E => ∫ θ in 0..T,
      (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2) μ := by
    simp only [intervalIntegral.integral_of_le hT.le]
    simpa only [Set.uIoc_of_le hT.le,Function.comp_apply,Prod.swap_prod_mk] using
      hi.swap.integral_prod_left
  have hdiff : Integrable (fun xy : E × E => (h xy.1-h xy.2)^2) μ := by
    exact ((memLp_lipschitz hl).comp_fst (stdGaussian E) |>.sub
      ((memLp_lipschitz hl).comp_snd (stdGaussian E))).integrable_sq
  have hb : (∫ xy : E × E, (h xy.1-h xy.2)^2 ∂μ) ≤
      T*∫ xy : E × E, (∫ θ in 0..T,
        (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hdiff (hinner.const_mul T)
    intro xy
    dsimp only
    have he : (h xy.1-h xy.2)^2 = (h xy.2-h xy.1)^2 := by ring_nf
    rw [he]
    exact rotation_difference_bound hh xy.1 xy.2
  dsimp [μ] at hb
  rw [independent_difference_variance (stdGaussian E) (memLp_lipschitz hl),
    ← intervalIntegral_integral_swap hi] at hb
  simp_rw [integral_tangent_sq hh hl] at hb
  rw [intervalIntegral.integral_const] at hb
  simp only [sub_zero,smul_eq_mul] at hb
  dsimp [T] at hb
  nlinarith

end GaussianPoincare
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def iterate (T : E → E) (σ : ℝ) : (n : ℕ) → E → (Fin n → E) → E
  | 0, x, _ => x
  | n+1, x, g => T (iterate T σ n x (fun i => g i.castSucc)) + σ • g (Fin.last n)

def energy (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => q^2*energy q n+1

lemma energy_nonneg {q : ℝ} (n : ℕ) : 0 ≤ energy q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [energy]; positivity

lemma energy_eq_sum (q : ℝ) (n : ℕ) : energy q n = ∑ j ∈ Finset.range n, q^(2*j) := by
  induction n with
  | zero => simp [energy]
  | succ n ih =>
      rw [energy,ih,Finset.sum_range_succ',Finset.mul_sum]
      simp only [Nat.mul_add,Nat.mul_one,pow_add]
      ring_nf

lemma energy_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    energy q n ≤ (1-q^2)⁻¹ := by
  have hp : 0 < 1-q^2 := by nlinarith
  induction n with
  | zero => simp only [energy]; positivity
  | succ n ih =>
      rw [energy]
      calc
        q^2*energy q n+1 ≤ q^2*(1-q^2)⁻¹+1 := by gcongr
        _ = (1-q^2)⁻¹ := by
          have hh := mul_inv_cancel₀ hp.ne'
          nlinarith only [hh]

lemma initial_contraction {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ) (n : ℕ) (x y : E) (g : Fin n → E) :
    dist (iterate T σ n x g) (iterate T σ n y g) ≤ (q:ℝ)^n*dist x y := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      simp only [iterate,dist_add_right]
      calc
        _ ≤ (q:ℝ)*dist (iterate T σ n x (fun i => g i.castSucc))
          (iterate T σ n y (fun i => g i.castSucc)) := hT.dist_le_mul _ _
        _ ≤ (q:ℝ)*((q:ℝ)^n*dist x y) :=
          mul_le_mul_of_nonneg_left (ih _) q.coe_nonneg
        _ = _ := by rw [pow_succ]; ring_nf

lemma noise_sensitivity {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) (x : E) (g k : Fin n → E) :
    dist (iterate T σ n x g) (iterate T σ n x k) ≤
      σ*Real.sqrt (energy q n)*Real.sqrt (∑ i, dist (g i) (k i)^2) := by
  induction n with
  | zero => simp [iterate,energy]
  | succ n ih =>
      let D := ∑ i : Fin n, dist (g i.castSucc) (k i.castSucc)^2
      let b := dist (g (Fin.last n)) (k (Fin.last n))
      let S := energy (q:ℝ) n
      have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hS : 0 ≤ S := energy_nonneg n
      have hb : 0 ≤ b := dist_nonneg
      have hd : dist (iterate T σ (n+1) x g) (iterate T σ (n+1) x k) ≤
          σ*((q:ℝ)*Real.sqrt S*Real.sqrt D+b) := by
        calc
          _ ≤ dist (T (iterate T σ n x (fun i => g i.castSucc)))
              (T (iterate T σ n x (fun i => k i.castSucc))) +
              dist (σ • g (Fin.last n)) (σ • k (Fin.last n)) := dist_add_add_le _ _ _ _
          _ ≤ (q:ℝ)*dist (iterate T σ n x (fun i => g i.castSucc))
                (iterate T σ n x (fun i => k i.castSucc)) + σ*b := by
            rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hσ]
            exact add_le_add (hT.dist_le_mul _ _) le_rfl
          _ ≤ (q:ℝ)*(σ*Real.sqrt S*Real.sqrt D)+σ*b := by
            exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) q.coe_nonneg) le_rfl
          _ = _ := by ring_nf
      have hc : ((q:ℝ)*Real.sqrt S*Real.sqrt D+b)^2 ≤
          ((q:ℝ)^2*S+1)*(D+b^2) := by
        calc
          _ ≤ (((q:ℝ)*Real.sqrt S)^2+1)*((Real.sqrt D)^2+b^2) := by
            nlinarith [sq_nonneg ((q:ℝ)*Real.sqrt S*b-Real.sqrt D)]
          _ = _ := by rw [mul_pow,Real.sq_sqrt hS,Real.sq_sqrt hD]
      have hr : (q:ℝ)*Real.sqrt S*Real.sqrt D+b ≤
          Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2) := by
        have hp : 0 ≤ Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2) := by positivity
        have he : (Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2))^2 =
            ((q:ℝ)^2*S+1)*(D+b^2) := by
          rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
        nlinarith
      rw [energy,Fin.sum_univ_castSucc]
      exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hr hσ])

lemma noise_lipschitz {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ≥0) (n : ℕ) (x : E) :
    LipschitzWith ⟨(σ:ℝ)*Real.sqrt (energy q n),by positivity⟩
      (fun g : PiLp 2 (fun _ : Fin n => E) => iterate T σ n x g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g k
  have hh := noise_sensitivity hT σ.coe_nonneg n x (fun i => g i) (fun i => k i)
  rw [← PiLp.dist_sq_eq_of_L2,Real.sqrt_sq (dist_nonneg)] at hh
  exact hh

lemma contDiff_iterate {T : E → E} (hT : ContDiff ℝ 1 T) (σ : ℝ) (n : ℕ)
    {x : F → E} (hx : ContDiff ℝ 1 x) {g : F → Fin n → E}
    (hg : ∀ i, ContDiff ℝ 1 (fun z => g z i)) :
    ContDiff ℝ 1 (fun z => iterate T σ n (x z) (g z)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      exact (hT.comp (ih (fun i => hg i.castSucc))).add ((hg (Fin.last n)).const_smul σ)

lemma contDiff_noise {T : E → E} (hT : ContDiff ℝ 1 T) (σ : ℝ) (n : ℕ) (x : E) :
    ContDiff ℝ 1 (fun g : PiLp 2 (fun _ : Fin n => E) => iterate T σ n x g) := by
  apply contDiff_iterate hT σ n contDiff_const
  intro i
  exact (PiLp.proj 2 (fun _ : Fin n => E) i : PiLp 2 (fun _ : Fin n => E) →L[ℝ] E).contDiff

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace GaussianPoincare
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in

theorem variance_lipschitz_image {T : E → F} (hT : ContDiff ℝ 1 T)
    {A : ℝ≥0} (hA : LipschitzWith A T) {h : F → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hK : LipschitzWith K h) :
    Var[h; (stdGaussian E).map T] ≤ (Real.pi^2/8)*(A:ℝ)^2*
      ∫ y, ‖fderiv ℝ h y‖^2 ∂(stdGaussian E).map T := by
  rw [variance_map hh.continuous.measurable.aemeasurable hT.continuous.measurable.aemeasurable]
  have hb := variance_le_gradient (hh.comp hT) (hK.comp hA)
  have hi : Integrable (fun x : E => ‖fderiv ℝ (h ∘ T) x‖^2) (stdGaussian E) := by
    apply Integrable.mono' (integrable_const (((K*A:ℝ≥0):ℝ)^2))
      (((hh.comp hT).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ (hK.comp hA)) 2
  have hj : Integrable (fun x : E => (A:ℝ)^2*‖fderiv ℝ h (T x)‖^2) (stdGaussian E) := by
    apply Integrable.mono' (integrable_const ((A:ℝ)^2*(K:ℝ)^2))
      (((hh.continuous_fderiv (by norm_num)).comp hT.continuous |>.norm.pow 2).const_mul
        ((A:ℝ)^2) |>.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(A:ℝ)^2*‖fderiv ℝ h (T x)‖^2‖ ≤ (A:ℝ)^2*(K:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2) (sq_nonneg _)
  have he : (∫ x, ‖fderiv ℝ (h ∘ T) x‖^2 ∂stdGaussian E) ≤
      (A:ℝ)^2*∫ x, ‖fderiv ℝ h (T x)‖^2 ∂stdGaussian E := by
    rw [← integral_const_mul]
    apply integral_mono hi hj
    intro x
    dsimp only
    rw [fderiv_comp x (hh.differentiable (by norm_num) (T x))
      (hT.differentiable (by norm_num) x)]
    have hb' := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ h (T x)) (fderiv ℝ T x)
    have hs : ‖(fderiv ℝ h (T x)).comp (fderiv ℝ T x)‖ ≤ ‖fderiv ℝ h (T x)‖*(A:ℝ) :=
      hb'.trans (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hA) (norm_nonneg _))
    have hc := pow_le_pow_left₀ (norm_nonneg _) hs 2
    simpa only [mul_pow,mul_comm] using hc
  have hmap : (∫ y, ‖fderiv ℝ h y‖^2 ∂(stdGaussian E).map T) =
      ∫ x, ‖fderiv ℝ h (T x)‖^2 ∂stdGaussian E :=
    integral_map hT.continuous.aemeasurable
      (((hh.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
  rw [hmap]
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ Real.pi^2/8 by positivity)])

end GaussianPoincare
end LogConcaveSampling

end UpperProof
end
end
end

end OAI

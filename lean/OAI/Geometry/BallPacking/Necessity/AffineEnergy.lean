import Mathlib
import OAI.Geometry.BallPacking.Necessity.AffineBubble

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def dirichletDensity {n : ℕ} (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (1,0)) +
  stdDot n (fderiv ℝ (realCurve u) z (0,1)) (fderiv ℝ (realCurve u) z (0,1))

def complexDefect {n : ℕ} (u : ℂ → Phase n) (z : Plane) : Phase n :=
  fderiv ℝ (realCurve u) z (0,1) - standardJ n (fderiv ℝ (realCurve u) z (1,0))

def defectDensity {n : ℕ} (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (complexDefect u z) (complexDefect u z)

def standardCurvePrimitive {n : ℕ} (u : ℂ → Phase n) : Plane → Plane →L[ℝ] ℝ :=
  planarPullback (realCurve u) stdPrimitive

theorem standardCurvePrimitive_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (standardCurvePrimitive u) :=
  planarPullback_smooth (realCurve_smooth hu) (stdPrimitive_smooth n)

theorem standardCurvePrimitive_curl {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (standardCurvePrimitive u) z =
      standardForm (fderiv ℝ (realCurve u) z (1,0))
        (fderiv ℝ (realCurve u) z (0,1)) := by
  rw [standardCurvePrimitive,planarPullback_curl (realCurve_smooth hu) (stdPrimitive_smooth n)]
  exact stdPrimitive_extDeriv _ _ _

theorem stdDot_defect_identity {n : ℕ} (v w : Phase n) :
    stdDot n v v + stdDot n w w =
      2 * standardForm v w + stdDot n (w-standardJ n v) (w-standardJ n v) := by
  simp only [stdDot_apply, standardForm, standardJ_apply, Pi.sub_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dirichlet_defect_identity {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (z : Plane) :
    dirichletDensity u z = 2 * planarCurl (standardCurvePrimitive u) z + defectDensity u z := by
  rw [standardCurvePrimitive_curl hu]
  exact stdDot_defect_identity _ _

theorem dirichletDensity_nonneg {n : ℕ} (u : ℂ → Phase n) (z : Plane) :
    0 ≤ dirichletDensity u z := add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

theorem dirichletDensity_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (dirichletDensity u) := by
  have hd := (realCurve_smooth hu).fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
  have hx := hd.clm_apply (contDiff_const (c := ((1,0):Plane)))
  have hy := hd.clm_apply (contDiff_const (c := ((0,1):Plane)))
  exact (((stdDot n).contDiff.comp hx).clm_apply hx).add
    (((stdDot n).contDiff.comp hy).clm_apply hy)

theorem defectDensity_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (defectDensity u) := by
  have hd := (realCurve_smooth hu).fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
  have hx := hd.clm_apply (contDiff_const (c := ((1,0):Plane)))
  have hy := hd.clm_apply (contDiff_const (c := ((0,1):Plane)))
  have he := hy.sub ((standardJ n).contDiff.comp hx)
  exact ((stdDot n).contDiff.comp he).clm_apply he

theorem outerCutoff_integral_tendsto {f : Plane → ℝ} (hf : Integrable f) :
    Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z) * f z)
      atTop (𝓝 (∫ z, f z)) := by
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
  · intro j
    exact (((outerProfile_smooth _).comp radiusSq_smooth).continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact hf.norm
  · intro j
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul,Real.norm_of_nonneg (outerProfile_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (outerProfile_le_one _ _)
  · apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hn.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    rw [outerProfile_one (by positivity) (radiusSq_nonneg z) hj,one_mul]

theorem outerCutoff_integrable {f : Plane → ℝ} (hf : Continuous f) {A : ℝ} (hA : 0<A) :
    Integrable (fun z => outerProfile A (radiusSq z)*f z) := by
  apply (((outerProfile_smooth A).comp radiusSq_smooth).continuous.mul hf).integrable_of_hasCompactSupport
  exact (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)).mul_right

theorem integrable_of_nonneg_of_outerCutoff_limit {f : Plane → ℝ}
    (hf : Continuous f) (hp : ∀ z, 0 ≤ f z) {E : ℝ}
    (hlim : Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*f z)
      atTop (𝓝 E)) : Integrable f ∧ (∫ z, f z) = E := by
  let g (j : ℕ) (z : Plane) := outerProfile ((j:ℝ)+1) (radiusSq z)*f z
  have hA (j : ℕ) : 0 < (j:ℝ)+1 := by positivity
  have hgpos (j : ℕ) (z : Plane) : 0 ≤ g j z := mul_nonneg (outerProfile_nonneg _ _) (hp z)
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hEn : 0 ≤ E := ge_of_tendsto hlim (Filter.Eventually.of_forall fun j => integral_nonneg (hgpos j))
  have hmeas (j : ℕ) : AEMeasurable (fun z => ENNReal.ofReal (g j z)) :=
    (ENNReal.continuous_ofReal.comp
      (((outerProfile_smooth _).comp radiusSq_smooth).continuous.mul hf)).aemeasurable
  have hmono : ∀ᵐ z : Plane, Monotone (fun j : ℕ => ENNReal.ofReal (g j z)) := by
    apply Filter.Eventually.of_forall
    intro z i j hij
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (outerProfile_mono (hA i) (by exact_mod_cast Nat.add_le_add_right hij 1)
        (radiusSq_nonneg z)) (hp z)
  have hpoint : ∀ᵐ z : Plane, Tendsto
      (fun j : ℕ => ENNReal.ofReal (g j z)) atTop (𝓝 (ENNReal.ofReal (f z))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hn.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    simp only [g,outerProfile_one (hA j) (radiusSq_nonneg z) hj,one_mul]
  have hm := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hpoint
  have heq (j : ℕ) : (∫⁻ z, ENNReal.ofReal (g j z)) = ENNReal.ofReal (∫ z, g j z) :=
    (ofReal_integral_eq_lintegral_ofReal (outerCutoff_integrable hf (hA j))
      (Filter.Eventually.of_forall (hgpos j))).symm
  simp_rw [heq] at hm
  have hmval := tendsto_nhds_unique hm (ENNReal.tendsto_ofReal hlim)
  have hi : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
    rw [hmval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp)
    hi.aestronglyMeasurable,hmval,ENNReal.toReal_ofReal hEn]

theorem AffineLineCurve.affine_remainder_extends {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ a : Phase n, a ≠ 0 ∧
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
      ∃ v : ℂ → Phase n, ContDiffAt ℝ ∞ v 0 ∧
        (fun z : ℂ => u z-z • a) =ᶠ[cocompact ℂ] fun z => v z⁻¹ := by
  obtain ⟨a,ha,hl⟩ := hu.2.2.2.2
  let V := infinityGerm u a
  have hV : AnalyticAt ℂ V 0 := infinityGerm_analyticAt (hu.holomorphic_at_infinity hc) hl
  have hV0 : V 0 = a := by simp [V,infinityGerm]
  obtain ⟨r,hr,hVr⟩ := hV.exists_ball_analyticOnNhd
  have hball : Metric.ball (0:ℂ) r ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ hr
  have hv := ((Complex.differentiableOn_dslope hball).mpr
    hVr.differentiableOn).analyticAt hball
  refine ⟨a,ha,hl,dslope V 0,hv.contDiffAt.restrict_scalars ℝ,?_⟩
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [dslope_of_ne V (inv_ne_zero hz0)]
  simp only [slope_def_module,sub_zero,inv_inv,V,infinityGerm,inv_ne_zero hz0,
    ite_false,ite_true,inv_inv,smul_sub,smul_smul,mul_inv_cancel₀ hz0,one_smul]

theorem standardCurvePrimitive_angular_limit_zero {n : ℕ} {u v : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹) :
    Tendsto (fun z : Plane => standardCurvePrimitive u z (planeRotation z))
      (cocompact Plane) (𝓝 0) := by
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hh := (affine_primitive_angular_limit_zero hv he (stdPrimitive_smooth n).continuous).comp hr
  apply hh.congr
  intro z
  change stdPrimitive _ _ = stdPrimitive _ _
  have hd := realCurve_fderiv (z := z) (hu.differentiable (by simp) _) (planeRotation z)
  rw [equivRealProd_rotation] at hd
  exact congrArg (stdPrimitive (u (Complex.equivRealProdCLM.symm z))) hd.symm

theorem affine_smooth {n : ℕ} (a : Phase n) : ContDiff ℝ ∞ (fun z : ℂ => z • a) :=
  (contDiff_id.smul (contDiff_const (c := a)) : ContDiff ℂ ∞ _).restrict_scalars ℝ

theorem realCurve_affine_fderiv {n : ℕ} (a : Phase n) (z w : Plane) :
    fderiv ℝ (realCurve (fun ζ : ℂ => ζ • a)) z w = Complex.equivRealProdCLM.symm w • a := by
  let A : Plane →L[ℝ] Phase n :=
    (((ContinuousLinearMap.id ℂ ℂ).smulRight a).restrictScalars ℝ).comp
      Complex.equivRealProdCLM.symm.toContinuousLinearMap
  change fderiv ℝ (A : Plane → Phase n) z w = _
  rw [A.fderiv]
  rfl

theorem complexDefect_sub_affine {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    complexDefect (fun ζ : ℂ => u ζ-ζ • a) z = complexDefect u z := by
  have he : realCurve (fun ζ : ℂ => u ζ-ζ • a) =
      realCurve u-realCurve (fun ζ : ℂ => ζ • a) := rfl
  unfold complexDefect
  rw [he,fderiv_sub ((realCurve_smooth hu).differentiable (by simp) z)
    ((realCurve_smooth (affine_smooth a)).differentiable (by simp) z)]
  simp only [sub_apply,realCurve_affine_fderiv,map_sub]
  have hx : Complex.equivRealProdCLM.symm ((1,0):Plane) = 1 := rfl
  have hy : Complex.equivRealProdCLM.symm ((0,1):Plane) = Complex.I := rfl
  rw [hx,hy,one_smul]
  change _ - Complex.I • a - (_ - Complex.I • a) = _
  abel

theorem defectDensity_sub_affine {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    defectDensity (fun z : ℂ => u z-z • a) = defectDensity u := by
  funext z
  simp only [defectDensity,complexDefect_sub_affine hu]

theorem affine_remainder_energy_identity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hdef : Integrable (defectDensity u)) :
    ∃ a : Phase n, a ≠ 0 ∧
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
      Integrable (dirichletDensity (fun z : ℂ => u z-z • a)) ∧
      (∫ z, dirichletDensity (fun ζ : ℂ => u ζ-ζ • a) z) = ∫ z, defectDensity u z := by
  obtain ⟨a,ha,hl,v,hv,he⟩ := hu.affine_remainder_extends hc
  let w : ℂ → Phase n := fun z => u z-z • a
  have hw : ContDiff ℝ ∞ w := hu.1.sub (affine_smooth a)
  have hcurl := (tendsto_integral_cutoffCurl (standardCurvePrimitive_smooth hw)
    (standardCurvePrimitive_angular_limit_zero hw hv he)).comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop :
        Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop))
  have hid (z : Plane) : dirichletDensity w z =
      2 * planarCurl (standardCurvePrimitive w) z + defectDensity u z := by
    rw [dirichlet_defect_identity hw]
    congr 1
    exact congrFun (defectDensity_sub_affine hu.1 a) z
  have hEq (j : ℕ) : (∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z) =
      2 * (∫ z, cutoffCurl (standardCurvePrimitive w) ((j:ℝ)+1) z) +
      ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*defectDensity u z := by
    have heq : (fun z => outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z) =
        fun z => 2 * cutoffCurl (standardCurvePrimitive w) ((j:ℝ)+1) z +
          outerProfile ((j:ℝ)+1) (radiusSq z)*defectDensity u z := by
      funext z
      rw [hid]
      unfold cutoffCurl
      ring
    rw [heq,integral_add ((cutoffCurl_integrable (standardCurvePrimitive_smooth hw)
      (by positivity)).const_mul 2) (outerCutoff_integrable (defectDensity_smooth hu.1).continuous
        (by positivity)),integral_const_mul]
  have hlim : Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z)
      atTop (𝓝 (∫ z, defectDensity u z)) := by
    simp_rw [hEq]
    convert (hcurl.const_mul 2).add (outerCutoff_integral_tendsto hdef) using 1 <;> simp
  obtain ⟨hwi,hwie⟩ := integrable_of_nonneg_of_outerCutoff_limit
    (dirichletDensity_smooth hw).continuous (dirichletDensity_nonneg w) hlim
  exact ⟨a,ha,hl,hwi,hwie⟩

theorem radialForm_joint_continuous {n : ℕ} {S T : ℝ} (hST : S < T) :
    Continuous (fun y : Phase n × Phase n × Phase n => radialForm S T y.1 y.2.1 y.2.2) := by
  have hc : Continuous (fun y : Phase n × Phase n × Phase n => capacity y.1) :=
    (capacity_smooth n).continuous.comp continuous_fst
  have hr := (radialCoefficient_smooth hST).continuous.comp hc
  have hs : Continuous (radialSlope S T) := by
    apply ((radialSwitch_smooth S T).continuous.neg).div
      ((continuous_const.add (radialOffset_smooth S T).continuous).pow 2)
    intro t
    exact pow_ne_zero 2 (ne_of_gt (show 0 < 1 + radialOffset S T t from by
      linarith [radialOffset_nonneg hST t]))
  have ho (a b : Phase n × Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => standardForm (a y) (b y)) := by
    simpa only [Function.comp_apply,stdOmega_apply] using ((stdOmega n).continuous.comp ha).clm_apply hb
  have hd (a b : Phase n × Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => stdDot n (a y) (b y)) :=
    ((stdDot n).continuous.comp ha).clm_apply hb
  exact (hr.mul (ho _ _ continuous_snd.fst continuous_snd.snd)).add
    ((continuous_const.mul (hs.comp hc)).mul
      (((hd _ _ continuous_fst continuous_snd.fst).mul (ho _ _ continuous_fst continuous_snd.snd)).sub
        ((hd _ _ continuous_fst continuous_snd.snd).mul (ho _ _ continuous_fst continuous_snd.fst))))

theorem stdDot_self_smul {n : ℕ} (a : ℝ) (v : Phase n) :
    stdDot n (a • v) (a • v) = a^2 * stdDot n v v := by
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

theorem homotopy_defect_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      stdDot n ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
        ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have h := (hj.sub (continuous_const (y := standardJ n)).continuousOn).clm_apply continuous_snd.continuousOn
  exact ((stdDot n).continuous.comp_continuousOn h).clm_apply h

theorem homotopy_radial_graph_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    {S T : ℝ} (hST : S<T) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      radialForm S T y.1.2 y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have hxy : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      (y.1.2, y.2, lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (continuous_fst.snd.continuousOn).prodMk
      (continuous_snd.continuousOn.prodMk (hj.clm_apply continuous_snd.continuousOn))
  simpa only [Function.comp_def] using (radialForm_joint_continuous (n := n) hST).comp_continuousOn hxy

 

theorem homotopy_defect_unit_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x → lineHomotopy J t x = standardJ n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ tsupport (fun x => J x-standardJ n), ∀ v : Phase n, ‖v‖ = 1 →
      stdDot n ((lineHomotopy J t x-standardJ n) v) ((lineHomotopy J t x-standardJ n) v) ≤
        C * radialForm S T x v (lineHomotopy J t x v) := by
  let K := tsupport (fun x => J x-standardJ n)
  let L := ((Icc (0:ℝ) 1) ×ˢ K) ×ˢ Metric.sphere (0:Phase n) 1
  let e (y : (ℝ × Phase n) × Phase n) :=
    stdDot n ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
      ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
  let d (y : (ℝ × Phase n) × Phase n) :=
    radialForm S T y.1.2 y.2 (lineHomotopy J y.1.1 y.1.2 y.2)
  have hL : IsCompact L := (isCompact_Icc.prod hc).prod (isCompact_sphere _ _)
  have hsub : L ⊆ (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    fun y hy => ⟨⟨hy.1.1,mem_univ _⟩,mem_univ _⟩
  have he : ContinuousOn e L := (homotopy_defect_continuousOn hJs hJ).mono hsub
  have hd : ContinuousOn d L := (homotopy_radial_graph_continuousOn hJs hJ hST).mono hsub
  have hdp (y : (ℝ × Phase n) × Phase n) (hy : y ∈ L) : 0 < d y := by
    have hv : y.2 ≠ 0 := by
      intro hv
      have hh := hy.2
      simp [hv] at hh
    exact radialForm_adapted_pos hST hT (lineHomotopy_compatible hJ hy.1.1)
      (hout y.1.1 hy.1.1) y.1.2 hv
  obtain ⟨C,hC,hCb⟩ := (hL.image_of_continuousOn (he.div hd (fun y hy => (hdp y hy).ne'))).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t ht x hx v hv
  have hl : ((t,x),v) ∈ L := by
    exact ⟨⟨ht,hx⟩, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩
  have hr := hCb _ (mem_image_of_mem (fun y => e y / d y) hl)
  exact (div_le_iff₀ (hdp _ hl)).mp ((le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs,Pi.div_apply] using hr))

 

theorem homotopy_defect_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x → lineHomotopy J t x = standardJ n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x v : Phase n,
      stdDot n ((lineHomotopy J t x-standardJ n) v) ((lineHomotopy J t x-standardJ n) v) ≤
        C * radialForm S T x v (lineHomotopy J t x v) := by
  obtain ⟨C,hC,hCb⟩ := homotopy_defect_unit_bound hJs hJ hc hST hT hout
  let K := tsupport (fun x => J x-standardJ n)
  refine ⟨C,hC,?_⟩
  intro t ht x v
  have hpos : 0 ≤ radialForm S T x v (lineHomotopy J t x v) := by
    by_cases hv : v = 0
    · simp [hv,radialForm, ←stdOmega_apply]
    · exact (radialForm_adapted_pos hST hT (lineHomotopy_compatible hJ ht) (hout t ht) x hv).le
  by_cases hx : x ∈ K
  · by_cases hv : v = 0
    · simp [hv,radialForm, ←stdOmega_apply]
    let w : Phase n := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp only [w,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hh := hCb t ht x hx w hw
    change stdDot n ((lineHomotopy J t x-standardJ n) w)
      ((lineHomotopy J t x-standardJ n) w) ≤
        C * radialForm S T x w (lineHomotopy J t x w) at hh
    dsimp only [w] at hh
    rw [radialForm_self_smul, (lineHomotopy J t x-standardJ n).map_smul,
      stdDot_self_smul] at hh
    have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))
    nlinarith
  · have he0 : lineHomotopy J t x-standardJ n = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun y => lineHomotopy J t y-standardJ n)
      exact fun hy => hx (lineHomotopy_support J ht hy)
    simp only [he0,zero_apply,map_zero]
    exact mul_nonneg hC.le hpos

theorem homotopy_affine_error_energy (n : ℕ) (_hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (_hpq : p ≠ q) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∃ v : Phase n, v ≠ 0 ∧
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v) ∧
        Integrable (dirichletDensity (fun z : ℂ => u z-z • v)) ∧
        (∫ z, dirichletDensity (fun z : ℂ => u z-z • v) z) ≤ C := by
  obtain ⟨S,T,hS,hST,hT,hout⟩ := exists_common_radial_interval hc hs
  obtain ⟨C,hC,hbound⟩ := homotopy_defect_bound hJs hJ hc hST hT hout
  refine ⟨C,hC,?_⟩
  intro t ht u hu
  have harea := hu.total_radial_area (lineHomotopy_compatible hJ ht)
    (lineHomotopy_compact hc ht) hST hT (hout t ht)
  have hdefb (z : Plane) : defectDensity u z ≤ C * curveDensity S T u z := by
    unfold defectDensity complexDefect curveDensity
    rw [realCurve_CR (hu.2.1 _)]
    exact hbound t ht _ _
  have hdefi : Integrable (defectDensity u) :=
    (harea.1.const_mul C).mono' (defectDensity_smooth hu.1).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (show 0 ≤ defectDensity u z from stdDot_nonneg _)]
        exact hdefb z)
  obtain ⟨v,hv,hl,hwi,hwe⟩ := affine_remainder_energy_identity hu (lineHomotopy_compact hc ht) hdefi
  refine ⟨v,hv,hl,hwi,?_⟩
  rw [hwe]
  have hi := integral_mono hdefi (harea.1.const_mul C) hdefb
  rwa [integral_const_mul,harea.2,mul_one] at hi

end HigherDimensionalBallPacking.Rigidity

end

end OAI

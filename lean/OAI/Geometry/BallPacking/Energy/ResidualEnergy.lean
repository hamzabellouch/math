import Mathlib
import OAI.Geometry.BallPacking.Fredholm.TranslationContinuity

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}
local instance reInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance reInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def lineResidualEnergy (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (geometricResidual u (Complex.equivRealProdCLM.symm z))
    (geometricResidual u (Complex.equivRealProdCLM.symm z))

lemma lineResidualEnergy_nonneg (u : ℂ → Phase n) (z : Plane) : 0≤lineResidualEnergy u z :=
  stdDot_nonneg _

lemma lineResidualEnergy_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (lineResidualEnergy u) := by
  have h := (geometricResidual_smooth hu).continuous.comp Complex.equivRealProdCLM.symm.continuous
  exact ((stdDot n).continuous.comp h).clm_apply h

lemma lineResidualEnergy_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (lineResidualEnergy u) := by
  have h := (geometricResidual_compact hu hJc).comp_left
    (g := fun v : Phase n => stdDot n v v) (by simp only [map_zero])
  exact h.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding

lemma geometricResidual_at_CR {J : Phase n → End n} {u : ℂ → Phase n} {z : ℂ}
    (hu : PseudoHolomorphicAt J u z) :
    geometricResidual u z=(J (u z)-standardJ n) (fderiv ℝ u z 1) := by
  have hh := hu.2 1
  simp only [mul_one] at hh
  rw [geometricResidual,hh]
  rfl

lemma realCurve_dx {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    fderiv ℝ (realCurve u) z (1,0)=fderiv ℝ u (Complex.equivRealProdCLM.symm z) 1 := by
  rw [realCurve_fderiv ((hu.differentiable (by simp)) _)]
  congr 1

lemma lineResidualEnergy_eq_defect {J : Phase n → End n} {u : ℂ → Phase n}
    (hus : ContDiff ℝ ∞ u) (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    lineResidualEnergy u z=defectEnergy (J (realCurve u z)) (fderiv ℝ (realCurve u) z (1,0)) := by
  rw [lineResidualEnergy,geometricResidual_at_CR (hu _),realCurve_dx hus]
  rfl

lemma lineHomotopy_outside {J : Phase n → End n} {S t : ℝ}
    (hout : ∀ x, S<capacity x → J x=standardJ n) (ht : t∈Icc (0:ℝ) 1)
    (x : Phase n) (hx : S<capacity x) : lineHomotopy J t x=standardJ n := by
  unfold lineHomotopy
  rw [hout x hx,interpolateJ_standard ht]

lemma residualEnergy_le_radialDensity {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {S T C : ℝ} (hST : S<T) (hT : T<1) (hC : 0≤C)
    (hout : ∀ x, S<capacity x → J x=standardJ n)
    (hbound : ∀ x∈closedBall n S, ∀ v : Phase n, defectEnergy (J x) v≤C*symplecticEnergy (J x) v)
    {u : ℂ → Phase n} (hus : ContDiff ℝ ∞ u) (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    lineResidualEnergy u z≤C*curveDensity S T u z := by
  rw [lineResidualEnergy_eq_defect hus hu]
  by_cases hx : capacity (realCurve u z)≤S
  · have hh := hbound (realCurve u z) hx (fderiv ℝ (realCurve u) z (1,0))
    have hd : curveDensity S T u z=symplecticEnergy (J (realCurve u z))
        (fderiv ℝ (realCurve u) z (1,0)) := by
      rw [curveDensity,realCurve_CR (hu _),radialForm_standard hST hx]
      rw [symplecticEnergy, stdOmega_apply]
    rwa [hd]
  · rw [hout _ (lt_of_not_ge hx),defectEnergy_standard]
    exact mul_nonneg hC (curveDensity_nonneg hST hT hJ hout hu z)

theorem exact_line_homotopy_residual_energy_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ C : ℝ, 0<C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (p q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u → (∫ z : Plane, lineResidualEnergy u z)≤C := by
  let K : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ closedBall n S
  have hK : IsCompact K := isCompact_Icc.prod (closedBall_isCompact n S)
  have hAc : ContinuousOn (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) K :=
    (lineHomotopy_smooth hJs hJ).continuousOn.mono (fun _ h => ⟨h.1,mem_univ _⟩)
  obtain ⟨C,hC,hbound⟩ := exists_defectEnergy_bound hK hAc
    (fun y hy => lineHomotopy_compatible hJ hy.1 y.2)
  refine ⟨C,hC,?_⟩
  intro t ht p q u hu
  have hcom := lineHomotopy_compact hJc ht
  have hcon := lineResidualEnergy_continuous hu.1
  have hec := lineResidualEnergy_compact hu hcom
  have hle : ∀ z : Plane, lineResidualEnergy u z≤C*curveDensity S T u z :=
    residualEnergy_le_radialDensity (lineHomotopy_compatible hJ ht) hST hT hC.le
      (lineHomotopy_outside hout ht) (fun x hx v => hbound (t,x) ⟨ht,hx⟩ v) hu.1 hu.2.1
  have hm := hu.compact_density_mass_le_one (lineHomotopy_compatible hJ ht) hcom hST hT
    (lineHomotopy_outside hout ht) (hcon.div_const C) (hec.comp_left (g := fun x : ℝ => x/C) (by simp))
    (fun z => (div_le_iff₀ hC).mpr (by simpa only [mul_comm C] using hle z))
  rw [integral_div] at hm
  have hres := (div_le_iff₀ hC).mp hm
  simpa only [one_mul] using hres


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def sourceRadialCutoff (A : ℝ) (z : Plane) : ℝ := outerProfile A (radiusSq z)

lemma sourceRadialCutoff_smooth (A : ℝ) : ContDiff ℝ ∞ (sourceRadialCutoff A) :=
  (outerProfile_smooth A).comp radiusSq_smooth

lemma sourceRadialCutoff_compact {A : ℝ} (hA : 0<A) : HasCompactSupport (sourceRadialCutoff A) :=
  HasCompactSupport.comp_radiusSq (outerProfile_compact hA)

lemma sourceRadialCutoff_nonneg (A : ℝ) (z : Plane) : 0 ≤ sourceRadialCutoff A z :=
  outerProfile_nonneg A _

lemma sourceRadialCutoff_le_one (A : ℝ) (z : Plane) : sourceRadialCutoff A z≤1 := by
  have h : 1≤radiusSq z+2 := by linarith [radiusSq_nonneg z]
  simp only [sourceRadialCutoff,outerProfile,Real.smoothTransition.one_of_one_le h,one_mul]
  linarith [Real.smoothTransition.nonneg ((radiusSq z-A)/A)]

lemma sourceRadialCutoff_eventually_one_on_compact {K : Set Plane} (hK : IsCompact K) :
    ∀ᶠ A : ℝ in atTop, ∀ z∈K, sourceRadialCutoff A z=1 := by
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  filter_upwards [eventually_ge_atTop B] with A hA z hz
  exact outerProfile_one_before (radiusSq_nonneg z) ((hbound z hz).le.trans hA) (hB.trans_le hA)

lemma sourceRadialCutoff_tendsto (z : Plane) :
    Tendsto (fun A : ℝ => sourceRadialCutoff A z) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact (isCompact_singleton (x := z))] with A hA
  exact (hA z (mem_singleton z)).symm

lemma smooth_cutoff_integrable_mul {A : ℝ} (hA : 0<A) {e : Plane → ℝ} (he : Continuous e) :
    Integrable (fun z => sourceRadialCutoff A z*e z) :=
  ((sourceRadialCutoff_smooth A).continuous.mul he).integrable_of_hasCompactSupport
    ((sourceRadialCutoff_compact hA).mul_right)

lemma radial_curl_integral_between {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A a b : ℝ} (hA : 0<A)
    (hb : ∀ z : Plane, A≤radiusSq z → a≤β z (planeRotation z) ∧ β z (planeRotation z)≤b) :
    2*Real.pi*a≤(∫ z, sourceRadialCutoff A z*planarCurl β z) ∧
      (∫ z, sourceRadialCutoff A z*planarCurl β z)≤2*Real.pi*b := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hc : HasCompactSupport g := outerProfile_compact hA
  have hpoint (z : Plane) :
      2*deriv g (radiusSq z)*b≤cutoffWedge (sourceRadialCutoff A) β z ∧
      cutoffWedge (sourceRadialCutoff A) β z≤2*deriv g (radiusSq z)*a := by
    rw [show sourceRadialCutoff A=fun y => g (radiusSq y) from rfl,cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z)=0
    · simp only [hd,mul_zero,zero_mul,le_refl,and_self]
    have hzA : A≤radiusSq z := by
      by_contra! hz
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hz)
    have hneg : 2*deriv g (radiusSq z)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (hb z hzA).2 hneg,
      mul_le_mul_of_nonpos_left (hb z hzA).1 hneg⟩
  have hdi (c : ℝ) : Integrable (fun z : Plane => 2*deriv g (radiusSq z)*c) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hc.deriv)).const_mul 2).mul_const c
  have hwi := cutoffWedge_integrable (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ
  have hlow := integral_mono (hdi b) hwi (fun z => (hpoint z).1)
  have hupp := integral_mono hwi (hdi a) (fun z => (hpoint z).2)
  have hg0 : g 0=1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hc,hg0,mul_one] at hlow hupp
  rw [integral_cutoffWedge (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ] at hlow hupp
  constructor <;> nlinarith only [hlow,hupp]

lemma radial_curl_integral_tendsto {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z*planarCurl β z)
      atTop (𝓝 (2*Real.pi*k)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp : 0<2*Real.pi := by positivity
  let δ := ε/(4*Real.pi)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hev : ∀ᶠ z in cocompact Plane,
      k-δ<β z (planeRotation z) ∧ β z (planeRotation z)<k+δ :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K,hK,hKb⟩ := mem_cocompact.mp hev
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  refine ⟨B,?_⟩
  intro A hA
  have hAp : 0<A := hB.trans_le hA
  have hh : ∀ z : Plane, A≤radiusSq z →
      k-δ≤β z (planeRotation z) ∧ β z (planeRotation z)≤k+δ := by
    intro z hz
    have hzK : z∉K := by
      intro hzK
      exact (not_lt_of_ge (hA.trans hz)) (hbound z hzK)
    exact ⟨(hKb hzK).1.le,(hKb hzK).2.le⟩
  have hb := radial_curl_integral_between hβ hAp hh
  rw [Real.dist_eq]
  apply abs_lt.mpr
  have he : 2*Real.pi*δ=ε/2 := by dsimp [δ]; field_simp; ring_nf
  constructor <;> nlinarith only [hb.1,hb.2,he,hε]

lemma compact_integral_cutoff_eventually {e : Plane → ℝ} (he : HasCompactSupport e) :
    ∀ᶠ A : ℝ in atTop, (fun z => sourceRadialCutoff A z*e z)=e := by
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact he] with A hA
  funext z
  by_cases hz : z∈tsupport e
  · rw [hA z hz,one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]



lemma integrable_of_radial_exhaustion_limit {e : Plane → ℝ}
    (he : Continuous e) (hn : ∀ z, 0 ≤ e z) {L : ℝ}
    (hlim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * e z) atTop (𝓝 L)) :
    Integrable e ∧ (∫ z, e z)=L := by
  let a : ℕ → ℝ := fun i => (i:ℝ)+1
  have ha : Tendsto a atTop atTop := tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  have hap (i : ℕ) : 0<a i := by dsimp [a]; positivity
  let f : ℕ → Plane → ℝ := fun i z => sourceRadialCutoff (a i) z * e z
  have hfn (i : ℕ) (z : Plane) : 0≤f i z := mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn _)
  have hfc (i : ℕ) : Continuous (f i) := (sourceRadialCutoff_smooth _).continuous.mul he
  have hfi (i : ℕ) : Integrable (f i) := smooth_cutoff_integrable_mul (hap i) he
  have hfl (z : Plane) : Tendsto (fun i => f i z) atTop (𝓝 (e z)) := by
    simpa only [one_mul, f, Function.comp_def] using ((sourceRadialCutoff_tendsto z).comp ha).mul_const (e z)
  have hlim' : Tendsto (fun i => ∫ z, f i z) atTop (𝓝 L) := hlim.comp ha
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℕ)) (μ := (volume : Measure Plane))
    (f := fun i z => ENNReal.ofReal (f i z)) (fun i => (hfc i).measurable.ennreal_ofReal.aemeasurable)
  have hpoint (z : Plane) : liminf (fun i => ENNReal.ofReal (f i z)) atTop=ENNReal.ofReal (e z) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hfl z)).liminf_eq
  simp only [hpoint] at hfat
  have hil : Tendsto (fun i => ∫⁻ z, ENNReal.ofReal (f i z)) atTop (𝓝 (ENNReal.ofReal L)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim'
    simpa only [Function.comp_def, ofReal_integral_eq_lintegral_ofReal (hfi _) (ae_of_all _ (hfn _))] using h
  rw [hil.liminf_eq] at hfat
  have hei : Integrable e := (lintegral_ofReal_ne_top_iff_integrable he.aestronglyMeasurable
    (ae_of_all _ hn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  refine ⟨hei,?_⟩
  have hdc := tendsto_integral_filter_of_dominated_convergence (F := fun A z => sourceRadialCutoff A z * e z) e
    (Eventually.of_forall fun A : ℝ =>
      ((sourceRadialCutoff_smooth A).continuous.mul he).aestronglyMeasurable)
    (Eventually.of_forall fun A : ℝ => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn z))]
      exact mul_le_of_le_one_left (hn z) (sourceRadialCutoff_le_one A z)) hei
    (ae_of_all _ fun z => by simpa only [one_mul] using (sourceRadialCutoff_tendsto z).mul_const (e z))
  exact tendsto_nhds_unique hdc hlim


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

def dirichletEnergy (v : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ (realCurve v) z (1,0)) (fderiv ℝ (realCurve v) z (1,0)) +
  stdDot n (fderiv ℝ (realCurve v) z (0,1)) (fderiv ℝ (realCurve v) z (0,1))

lemma dirichletEnergy_nonneg (v : ℂ → Phase n) (z : Plane) : 0≤dirichletEnergy v z :=
  add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

lemma dirichletEnergy_continuous {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (dirichletEnergy v) := by
  have hd := ((realCurve_smooth hv).fderiv_right (m := ∞) (by simp)).continuous
  have hx := hd.clm_apply (continuous_const (y := ((1,0):Plane)))
  have hy := hd.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact (((stdDot n).continuous.comp hx).clm_apply hx).add (((stdDot n).continuous.comp hy).clm_apply hy)

lemma residual_energy_algebra (x y : Phase n) :
    stdDot n x x+stdDot n y y-stdDot n (y-standardJ n x) (y-standardJ n x)=2*stdOmega n x y := by
  simp only [map_sub,sub_apply,stdDot_J_right,stdOmega_apply]
  rw [stdDot_symm (standardJ n x) y,stdDot_J_right,standardForm_skew (standardJ n x) x,standardForm_J_right,
    standardForm_skew y x]
  ring

lemma lineResidualEnergy_real {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    lineResidualEnergy u z=stdDot n
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0)))
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0))) := by
  simp only [realCurve_fderiv (hu.differentiable (by simp) _)]
  rfl

lemma standard_primitive_curl {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) (z : Plane) :
    planarCurl (planarPullback (realCurve v) (stdOmega n)) z=
      dirichletEnergy v z-lineResidualEnergy v z := by
  rw [planarPullback_curl (realCurve_smooth hv) (stdOmega n).contDiff,
    oneForm_extDeriv_apply (stdOmega n).differentiableAt,(stdOmega n).fderiv]
  rw [lineResidualEnergy_real hv]
  change stdOmega n _ _-stdOmega n _ _ = _
  rw [dirichletEnergy,residual_energy_algebra,stdOmega_apply,stdOmega_apply,standardForm_skew]
  ring

lemma affineCorrection_residual {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    geometricResidual (affineCorrection u a)=geometricResidual u := by
  funext z
  have hlin := (hasFDerivAt_id (𝕜 := ℝ) z).smul_const a
  have hd := (hu.differentiable (by simp) z).hasFDerivAt.sub hlin
  change HasFDerivAt (affineCorrection u a) _ z at hd
  rw [geometricResidual,hd.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,smul_sub,one_smul,geometricResidual]
  abel

lemma affineCorrection_residual_energy {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    lineResidualEnergy (affineCorrection u a)=lineResidualEnergy u := by
  funext z
  simp only [lineResidualEnergy,affineCorrection_residual hu]

lemma affineCorrection_real_flux_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {a : Phase n} {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0)
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : Plane => planarPullback (realCurve (affineCorrection u a)) (stdOmega n) z
      (planeRotation z)) (cocompact Plane) (𝓝 0) := by
  have ht := (affineCorrection_primitive_flux_zero hh he).comp
    (le_of_eq Complex.equivRealProdCLM.symm.toHomeomorph.map_cocompact)
  convert ht using 1
  funext z
  rw [planarPullback]
  simp only [ContinuousLinearMap.comp_apply]
  rw [realCurve_fderiv ((affineCorrection_smooth hu a).differentiable (by simp) _),equivRealProd_rotation]
  rfl

theorem AffineLineCurve.affine_correction_energy {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ a : Phase n, a≠0 ∧ Integrable (dirichletEnergy (affineCorrection u a)) ∧
      (∫ z, dirichletEnergy (affineCorrection u a) z)=∫ z, lineResidualEnergy u z := by
  obtain ⟨a,h,ha,hh,he⟩ := hu.affine_correction_at_infinity hJc
  have hv := affineCorrection_smooth hu.1 a
  have hβ := planarPullback_smooth (realCurve_smooth hv) (stdOmega n).contDiff
  have hlim := radial_curl_integral_tendsto hβ (affineCorrection_real_flux_zero hu.1 hh he)
  simp only [mul_zero] at hlim
  have hfl : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * lineResidualEnergy u z)
      atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [compact_integral_cutoff_eventually (lineResidualEnergy_compact hu hJc)] with A hA
    rw [hA]
  have helim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z *
      dirichletEnergy (affineCorrection u a) z) atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    have hl := hlim.add hfl
    simp only [zero_add] at hl
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
    rw [←integral_add
      (smooth_cutoff_integrable_mul hA ((planarCurl_contDiff hβ).continuous))
      (smooth_cutoff_integrable_mul hA (lineResidualEnergy_continuous hu.1))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [standard_primitive_curl hv,affineCorrection_residual_energy hu.1]
    ring
  exact ⟨a,ha,integrable_of_radial_exhaustion_limit (dirichletEnergy_continuous hv)
    (dirichletEnergy_nonneg _) helim⟩


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self (x y : Phase n) :
    stdDot n (x-y) (x-y)=stdDot n x x-2*stdDot n x y+stdDot n y y := by
  simp only [map_sub,sub_apply]
  rw [stdDot_symm y x]
  ring

lemma stdOmega_le_half_energy (x y : Phase n) :
    stdOmega n x y≤(stdDot n x x+stdDot n y y)/2 := by
  have h := stdDot_standardForm_sq_le x y
  have hx := stdDot_nonneg x
  have hy := stdDot_nonneg y
  rw [stdOmega_apply]
  nlinarith [sq_nonneg (stdDot n x y),sq_nonneg (stdDot n x x-stdDot n y y)]

lemma interval_integral_stdDot_const {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t) v)=stdDot n (∫ t in a..b, f t) v :=
  ((stdDot n).flip v).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

lemma interval_stdDot_variance {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t-v) (f t-v))=
      (∫ t in a..b, stdDot n (f t) (f t))-2*stdDot n (∫ t in a..b, f t) v+
        (b-a)*stdDot n v v := by
  have he : Continuous (fun t => stdDot n (f t) (f t)) := ((stdDot n).continuous.comp hf).clm_apply hf
  have hv : Continuous (fun t => 2*stdDot n (f t) v) := continuous_const.mul
    (((stdDot n).continuous.comp hf).clm_apply continuous_const)
  simp_rw [stdDot_sub_self]
  have hei : IntervalIntegrable (fun t => stdDot n (f t) (f t)-2*stdDot n (f t) v) volume a b :=
    (he.sub hv).intervalIntegrable a b
  rw [intervalIntegral.integral_add hei intervalIntegrable_const,
    intervalIntegral.integral_sub (he.intervalIntegrable a b) (hv.intervalIntegrable a b),
    intervalIntegral.integral_const_mul,interval_integral_stdDot_const hf,
    intervalIntegral.integral_const,smul_eq_mul]

lemma interval_stdDot_integral_sq_le {f : ℝ → Phase n} (hf : Continuous f) {a b : ℝ} (hab : a≤b) :
    stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t)≤(b-a)*(∫ t in a..b, stdDot n (f t) (f t)) := by
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst b
    simp only [intervalIntegral.integral_same,sub_self,zero_mul,map_zero,le_refl]
  have hL : 0<b-a := sub_pos.mpr hab'
  let v : Phase n := (b-a)⁻¹ • (∫ t in a..b, f t)
  have hv := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun t => stdDot_nonneg (f t-v))
  rw [interval_stdDot_variance hf] at hv
  have hm := mul_nonneg hL.le hv
  have hid : (b-a)*((∫ t in a..b, stdDot n (f t) (f t))-
      2*stdDot n (∫ t in a..b, f t) v+(b-a)*stdDot n v v)=
      (b-a)*(∫ t in a..b, stdDot n (f t) (f t))-
        stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma curve_chord_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b t : ℝ}
    (hat : a≤t) (htb : t≤b) :
    stdDot n (v t-v a) (v t-v a)≤(b-a)*(∫ s in a..b, stdDot n (deriv v s) (deriv v s)) := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hf : (∫ s in a..t, deriv v s)=v t-v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => (hv.differentiable (by simp) s).hasDerivAt)
      (hd.intervalIntegrable a t)
  have hj := interval_stdDot_integral_sq_le hd hat
  rw [hf] at hj
  have hec : Continuous (fun s => stdDot n (deriv v s) (deriv v s)) :=
    ((stdDot n).continuous.comp hd).clm_apply hd
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hec.intervalIntegrable a t)
    (hec.intervalIntegrable t b)
  have h1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hat (fun s => stdDot_nonneg (deriv v s))
  have h2 := intervalIntegral.integral_nonneg_of_forall (μ := volume) htb (fun s => stdDot_nonneg (deriv v s))
  nlinarith

theorem loop_symplectic_flux_le_energy {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a≤b) (hloop : v b=v a) :
    (∫ t in a..b, stdOmega n (v t) (deriv v t))≤
      ((b-a)^2+1)/2*(∫ t in a..b, stdDot n (deriv v t) (deriv v t)) := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hec : Continuous (fun t => stdDot n (deriv v t) (deriv v t)) :=
    ((stdDot n).continuous.comp hd).clm_apply hd
  have hfc : Continuous (fun t => stdOmega n (v t) (deriv v t)) :=
    ((stdOmega n).continuous.comp hv.continuous).clm_apply hd
  have hbc : Continuous (fun t => stdOmega n (v a) (deriv v t)) := (stdOmega n (v a)).continuous.comp hd
  have hent : (∫ t in a..b, deriv v t)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (hv.differentiable (by simp) s).hasDerivAt) (hd.intervalIntegrable a b),hloop,sub_self]
  have hb : (∫ t in a..b, stdOmega n (v a) (deriv v t))=0 := by
    rw [(stdOmega n (v a)).intervalIntegral_comp_comm (hd.intervalIntegrable a b),hent,map_zero]
  have hsub : (∫ t in a..b, stdOmega n (v t-v a) (deriv v t))=
      (∫ t in a..b, stdOmega n (v t) (deriv v t)) := by
    simp only [map_sub,sub_apply]
    rw [intervalIntegral.integral_sub (hfc.intervalIntegrable a b) (hbc.intervalIntegrable a b),hb,sub_zero]
  rw [←hsub]
  let E : ℝ := ∫ s in a..b, stdDot n (deriv v s) (deriv v s)
  have hp (t : ℝ) (ht : t∈Icc a b) : stdOmega n (v t-v a) (deriv v t)≤
      ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2 := by
    have hch := curve_chord_energy_le hv ht.1 ht.2
    have hω := stdOmega_le_half_energy (v t-v a) (deriv v t)
    dsimp only [E]
    linarith
  have hsc : Continuous (fun t => stdOmega n (v t-v a) (deriv v t)) :=
    ((stdOmega n).continuous.comp (hv.continuous.sub continuous_const)).clm_apply hd
  have huc : Continuous (fun t => ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2) :=
    (continuous_const.add hec).div_const 2
  have hl := intervalIntegral.integral_mono_on (μ := volume) hab (hsc.intervalIntegrable a b)
    (huc.intervalIntegrable a b) hp
  have heval : (∫ t in a..b, ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2)=((b-a)^2+1)/2*E := by
    rw [intervalIntegral.integral_div,intervalIntegral.integral_add intervalIntegrable_const
      (hec.intervalIntegrable a b),intervalIntegral.integral_const,smul_eq_mul]
    change ((b-a)*((b-a)*E)+E)/2=_
    ring
  rw [heval] at hl
  exact hl


local instance caInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance caInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def curveAreaDensity (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdOmega n (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1))

lemma curveAreaDensity_nonneg {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    {u : ℂ → Phase n} (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    0≤curveAreaDensity u z := by
  rw [curveAreaDensity,realCurve_CR (hu _),stdOmega_apply]
  by_cases hv : fderiv ℝ (realCurve u) z (1,0)=0
  · rw [hv,map_zero]
    simp [standardForm]
  · exact ((hJ _).2.2 _ hv).le

lemma dirichletEnergy_eq_residual_add_area {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    dirichletEnergy u z=lineResidualEnergy u z+2*curveAreaDensity u z := by
  have h := residual_energy_algebra (fderiv ℝ (realCurve u) z (1,0))
    (fderiv ℝ (realCurve u) z (0,1))
  rw [←lineResidualEnergy_real hu] at h
  change dirichletEnergy u z-lineResidualEnergy u z=2*curveAreaDensity u z at h
  linarith

lemma uniform_homotopy_pointwise_calibration {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) {S : ℝ}
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ C : ℝ, 0<C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (u : ℂ → Phase n),
      ContDiff ℝ ∞ u → (∀ z, PseudoHolomorphicAt (lineHomotopy J t) u z) →
        ∀ z, dirichletEnergy u z≤C*curveAreaDensity u z := by
  let K : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ closedBall n S
  have hK : IsCompact K := isCompact_Icc.prod (closedBall_isCompact n S)
  have hAc : ContinuousOn (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) K :=
    (lineHomotopy_smooth hJs hJ).continuousOn.mono (fun _ h => ⟨h.1,mem_univ _⟩)
  obtain ⟨B,hB,hbound⟩ := exists_defectEnergy_bound hK hAc
    (fun y hy => lineHomotopy_compatible hJ hy.1 y.2)
  refine ⟨B+2,by linarith,?_⟩
  intro t ht u hus hu z
  have hn := curveAreaDensity_nonneg (lineHomotopy_compatible hJ ht) hu z
  have hle : lineResidualEnergy u z≤B*curveAreaDensity u z := by
    rw [lineResidualEnergy_eq_defect hus hu]
    by_cases hx : capacity (realCurve u z)≤S
    · convert hbound (t,realCurve u z) ⟨ht,hx⟩ (fderiv ℝ (realCurve u) z (1,0)) using 1
      rw [curveAreaDensity,realCurve_CR (hu _)]
      rfl
    · rw [lineHomotopy_outside hout ht _ (lt_of_not_ge hx),defectEnergy_standard]
      exact mul_nonneg hB.le hn
  rw [dirichletEnergy_eq_residual_add_area hus]
  nlinarith only [hle]

theorem exact_line_homotopy_correction_energy_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ C : ℝ, 0<C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (p q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
        ∃ a : Phase n, a≠0 ∧ Integrable (dirichletEnergy (affineCorrection u a)) ∧
          (∫ z, dirichletEnergy (affineCorrection u a) z)≤C := by
  obtain ⟨C,hC,hbound⟩ := exact_line_homotopy_residual_energy_bound hJs hJ hJc hST hT hout
  refine ⟨C,hC,?_⟩
  intro t ht p q u hu
  obtain ⟨a,ha,hi,he⟩ := hu.affine_correction_energy (lineHomotopy_compact hJc ht)
  exact ⟨a,ha,hi,he ▸ hbound t ht p q u hu⟩



end HigherDimensionalBallPacking.Rigidity
end

end OAI

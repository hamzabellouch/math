import OAI.Analysis.NodalLength.Subharmonic

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

variable {X : Type*} [PseudoMetricSpace X]

def truncBelow (V : X → EReal) (n : ℕ) (x : X) : ℝ :=
  (max (V x) ((-(n:ℝ):ℝ):EReal)).toReal

omit [PseudoMetricSpace X] in
lemma coe_truncBelow {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    (truncBelow V n x:EReal)=max (V x) ((-(n:ℝ):ℝ):EReal) := by
  apply EReal.coe_toReal
  · apply ne_of_lt
    exact max_lt (hx.trans_lt (by simp)) (EReal.coe_lt_top _)
  · exact ne_of_gt ((EReal.bot_lt_coe (-(n:ℝ))).trans_le (le_max_right _ _))

omit [PseudoMetricSpace X] in
lemma truncBelow_nonpos {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    truncBelow V n x≤0 := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx]
  exact max_le hx (by exact_mod_cast (neg_nonpos.mpr (Nat.cast_nonneg n):-(n:ℝ)≤0))

omit [PseudoMetricSpace X] in
lemma truncBelow_lower {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    -(n:ℝ)≤truncBelow V n x := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx]
  exact le_max_right _ _

omit [PseudoMetricSpace X] in
lemma truncBelow_antitone {V : X → EReal} {x : X} (hx : V x≤0) :
    Antitone (fun n => truncBelow V n x) := by
  intro m n hmn
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx,coe_truncBelow hx]
  exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hmn)))

def supRegularize (K : Set X) (V : X → EReal) (n : ℕ) (x : X) : ℝ :=
  ⨆ y : K, truncBelow V n y-(n:ℝ)*dist x y

lemma regularize_bdd {K : Set X} {V : X → EReal} (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) :
    BddAbove (Set.range fun y : K => truncBelow V n y-(n:ℝ)*dist x y) := by
  refine ⟨0,?_⟩
  rintro _ ⟨y,rfl⟩
  exact sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans (mul_nonneg (Nat.cast_nonneg n) dist_nonneg))

lemma supRegularize_nonpos {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) : supRegularize K V n x≤0 := by
  let : Nonempty K := hK.to_subtype
  exact ciSup_le (fun y => sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans
    (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)))

lemma supRegularize_majorant {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) (n : ℕ) {x : X} (hx : x∈K) : V x≤(supRegularize K V n x:EReal) := by
  apply (le_max_left (V x) ((-(n:ℝ):ℝ):EReal)).trans
  rw [← coe_truncBelow (hV x hx)]
  apply EReal.coe_le_coe_iff.mpr
  have := le_ciSup (regularize_bdd hV n x) (⟨x,hx⟩:K)
  simpa only [supRegularize,Subtype.coe_mk,dist_self,mul_zero,sub_zero] using this

lemma supRegularize_antitone {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (x : X) : Antitone (fun n => supRegularize K V n x) := by
  let : Nonempty K := hK.to_subtype
  intro m n hmn
  apply ciSup_le
  intro y
  apply le_trans _ (le_ciSup (regularize_bdd hV m x) y)
  exact sub_le_sub (truncBelow_antitone (hV y y.2) hmn)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) dist_nonneg)

lemma supRegularize_lipschitz {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) : LipschitzWith (n:ℝ≥0) (supRegularize K V n) := by
  let : Nonempty K := hK.to_subtype
  have hdiff (x y : X) : supRegularize K V n x≤ supRegularize K V n y+(n:ℝ)*dist x y := by
    apply ciSup_le
    intro z
    have hle := le_ciSup (regularize_bdd hV n y) z
    change truncBelow V n z-(n:ℝ)*dist y z≤ supRegularize K V n y at hle
    have hd := dist_triangle_right y z x
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hd hn
    simp only [dist_comm y x,dist_comm (z:X) x] at hm
    linarith
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq,abs_le]
  have hxy := hdiff x y
  have hyx := hdiff y x
  simp only [dist_comm y x,NNReal.coe_natCast] at hyx ⊢
  constructor <;> linarith

lemma supRegularize_eventually_below {K : Set X} {V : X → EReal}
    (hV : ∀ x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) {a : ℝ} (ha : V x<(a:EReal)) :
    ∃ n : ℕ, supRegularize K V n x≤a := by
  let : Nonempty K := ⟨⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhdsWithin_iff.mp (husc a ha)
  obtain ⟨n,hn⟩ := exists_nat_gt (max (-a) (-a/δ))
  have hna : -(n:ℝ)≤a := by have := (le_max_left (-a) (-a/δ)).trans_lt hn; linarith
  have hnδ : -a<(n:ℝ)*δ := (div_lt_iff₀ hδ).mp ((le_max_right (-a) (-a/δ)).trans_lt hn)
  refine ⟨n,?_⟩
  apply ciSup_le
  intro y
  by_cases hd : dist x y<δ
  · have hy : V y<(a:EReal) := hnear ⟨by simpa only [Metric.mem_ball,dist_comm] using hd,y.2⟩
    have htr : truncBelow V n y≤a := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncBelow (hV y y.2)]
      exact max_le hy.le (EReal.coe_le_coe_iff.mpr hna)
    exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)).trans htr
  · have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hd) (Nat.cast_nonneg n : 0≤(n:ℝ))
    have ht := truncBelow_nonpos (n:=n) (hV y y.2)
    linarith

lemma iInf_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    (⨅ n : ℕ, (supRegularize K V n x:EReal))=V x := by
  apply le_antisymm
  · by_contra h
    obtain ⟨a,ha,ha'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
    obtain ⟨n,hn⟩ := supRegularize_eventually_below hV hx husc ha
    exact (not_le_of_gt ha') ((iInf_le (fun n => (supRegularize K V n x:EReal)) n).trans (EReal.coe_le_coe_iff.mpr hn))
  · exact le_iInf (fun n => supRegularize_majorant hV n hx)

lemma tendsto_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    Tendsto (fun n => (supRegularize K V n x:EReal)) atTop (𝓝 (V x)) := by
  rw [← iInf_supRegularize hV hx husc]
  exact tendsto_atTop_iInf (EReal.coe_strictMono.monotone.comp_antitone
    (supRegularize_antitone ⟨x,hx⟩ hV x))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def circleParameterMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioc 0 (2*Real.pi))

lemma circleAverage_eq_integral_parameter (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r=∫ t, f (circleMap c r t) ∂circleParameterMeasure := by
  rw [circleParameterMeasure,integral_smul_measure,Real.circleAverage,
    intervalIntegral.integral_of_le (by positivity)]
  simp only [ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]

lemma circleParameter_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f circleParameterMeasure := by
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : 0≤2*Real.pi)).mp
    (hf.intervalIntegrable 0 (2*Real.pi))).smul_measure ENNReal.ofReal_ne_top

lemma toENNReal_coe_real (x : ℝ) : (x:EReal).toENNReal=ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x),EReal.toReal_coe]

theorem circle_submean {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall a r⊆Ω) :
    (∫⁻ t, (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal
      ∂circleParameterMeasure) ≤ (-V a).toENNReal := by
  let K := Metric.sphere a r
  have hK : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKΩ : K⊆Ω := Metric.sphere_subset_closedBall.trans hball
  have hnegK : ∀ x∈K,V x≤0 := fun x hx => hneg x (hKΩ hx)
  let g : ℕ → ℂ → ℝ := fun n z => supRegularize K V n (planeComplex.symm z)
  have hg (n : ℕ) : Continuous (g n) :=
    (supRegularize_lipschitz hK hnegK n).continuous.comp planeComplex.symm.continuous
  let p : ℝ → Plane := fun t => planeComplex.symm (circleMap (planeComplex a) r t)
  have hpK (t : ℝ) : p t∈K := by
    change dist (planeComplex.symm (circleMap (planeComplex a) r t)) a=r
    rw [← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    simpa only [planeComplex.apply_symm_apply] using Metric.mem_sphere.mp (circleMap_mem_sphere (planeComplex a) hr.le t)
  have hlim (t : ℝ) : Tendsto (fun n => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t)))
      atTop (𝓝 ((-V (p t)).toENNReal)) := by
    have h := (tendsto_supRegularize hnegK (hpK t)
      ((hV _ (hKΩ (hpK t))).mono hKΩ)).neg
    have h' := EReal.continuous_toENNReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def,← EReal.coe_neg,toENNReal_coe_real,g,p] using h'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t))
  have hf (n : ℕ) : Measurable (f n) := by
    exact ENNReal.continuous_ofReal.measurable.comp ((hg n).comp (continuous_circleMap _ _)).neg.measurable
  have hmono : Monotone f := by
    intro m n hmn t
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (supRegularize_antitone hK hnegK (p t) hmn))
  have hiSup (t : ℝ) : (⨆ n,f n t)=(-V (p t)).toENNReal :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun m n hmn => hmono hmn t)) (hlim t)
  change (∫⁻ t,(-V (p t)).toENNReal ∂circleParameterMeasure)≤_
  simp_rw [← hiSup]
  rw [lintegral_iSup hf hmono]
  apply iSup_le
  intro n
  have hfn : Continuous (fun t => -g n (circleMap (planeComplex a) r t)) :=
    ((hg n).comp (continuous_circleMap _ _)).neg
  have hfnpos : ∀t,0≤ -g n (circleMap (planeComplex a) r t) :=
    fun t => neg_nonneg.mpr (supRegularize_nonpos hK hnegK n (p t))
  rw [← ofReal_integral_eq_lintegral_ofReal (circleParameter_integrable hfn) (Filter.Eventually.of_forall hfnpos)]
  rw [integral_neg,← circleAverage_eq_integral_parameter]
  rw [← toENNReal_coe_real, EReal.coe_neg]
  apply EReal.toENNReal_le_toENNReal
  apply EReal.neg_le_neg_iff.mpr
  apply submean_continuous_majorant hV (fun x hx => ne_of_lt ((hneg x hx).trans_lt (by simp))) htest hr hball (hg n)
  intro x hx
  simpa only [g,planeComplex.symm_apply_apply] using supRegularize_majorant hnegK n hx
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def polarParameterMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioo (-Real.pi) Real.pi)

lemma circleAverage_eq_integral_polar (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r=∫ t, f (circleMap c r t) ∂polarParameterMeasure := by
  have heq := ((periodic_circleMap c r).comp f).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [Function.comp_def,zero_add, show -Real.pi+2*Real.pi=Real.pi by ring] at heq
  rw [polarParameterMeasure,integral_smul_measure,Real.circleAverage,heq,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),integral_Ioc_eq_integral_Ioo]
  simp only [ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]

lemma polarParameter_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f polarParameterMeasure := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [restrict_Ioo_eq_restrict_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)).mp
    (hf.intervalIntegrable (-Real.pi) Real.pi)

theorem circle_submean_polar {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall a r⊆Ω) :
    (∫⁻ t, (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal
      ∂polarParameterMeasure) ≤ (-V a).toENNReal := by
  let K := Metric.sphere a r
  have hK : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKΩ : K⊆Ω := Metric.sphere_subset_closedBall.trans hball
  have hnegK : ∀ x∈K,V x≤0 := fun x hx => hneg x (hKΩ hx)
  let g : ℕ → ℂ → ℝ := fun n z => supRegularize K V n (planeComplex.symm z)
  have hg (n : ℕ) : Continuous (g n) :=
    (supRegularize_lipschitz hK hnegK n).continuous.comp planeComplex.symm.continuous
  let p : ℝ → Plane := fun t => planeComplex.symm (circleMap (planeComplex a) r t)
  have hpK (t : ℝ) : p t∈K := by
    change dist (planeComplex.symm (circleMap (planeComplex a) r t)) a=r
    rw [← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    simpa only [planeComplex.apply_symm_apply] using Metric.mem_sphere.mp (circleMap_mem_sphere (planeComplex a) hr.le t)
  have hlim (t : ℝ) : Tendsto (fun n => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t)))
      atTop (𝓝 ((-V (p t)).toENNReal)) := by
    have h := (tendsto_supRegularize hnegK (hpK t)
      ((hV _ (hKΩ (hpK t))).mono hKΩ)).neg
    have h' := EReal.continuous_toENNReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def,← EReal.coe_neg,toENNReal_coe_real,g,p] using h'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t))
  have hf (n : ℕ) : Measurable (f n) := by
    exact ENNReal.continuous_ofReal.measurable.comp ((hg n).comp (continuous_circleMap _ _)).neg.measurable
  have hmono : Monotone f := by
    intro m n hmn t
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (supRegularize_antitone hK hnegK (p t) hmn))
  have hiSup (t : ℝ) : (⨆ n,f n t)=(-V (p t)).toENNReal :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun m n hmn => hmono hmn t)) (hlim t)
  change (∫⁻ t,(-V (p t)).toENNReal ∂polarParameterMeasure)≤_
  simp_rw [← hiSup]
  rw [lintegral_iSup hf hmono]
  apply iSup_le
  intro n
  have hfn : Continuous (fun t => -g n (circleMap (planeComplex a) r t)) :=
    ((hg n).comp (continuous_circleMap _ _)).neg
  have hfnpos : ∀t,0≤ -g n (circleMap (planeComplex a) r t) :=
    fun t => neg_nonneg.mpr (supRegularize_nonpos hK hnegK n (p t))
  rw [← ofReal_integral_eq_lintegral_ofReal (polarParameter_integrable hfn) (Filter.Eventually.of_forall hfnpos)]
  rw [integral_neg,← circleAverage_eq_integral_polar]
  rw [← toENNReal_coe_real, EReal.coe_neg]
  apply EReal.toENNReal_le_toENNReal
  apply EReal.neg_le_neg_iff.mpr
  apply submean_continuous_majorant hV (fun x hx => ne_of_lt ((hneg x hx).trans_lt (by simp))) htest hr hball (hg n)
  intro x hx
  simpa only [g,planeComplex.symm_apply_apply] using supRegularize_majorant hnegK n hx
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Set MeasureTheory Filter
namespace SharpNodal.Profiles
open Carleman

lemma polarCoord_eq_circleMap (r t : ℝ) : Complex.polarCoord.symm (r,t)=circleMap 0 r t := by
  simp only [Complex.polarCoord_symm_apply,circleMap,zero_add]
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_cos,Complex.ofReal_sin]

lemma lintegral_radius {R : ℝ} (hR : 0≤R) :
    (∫⁻ r in Ioo 0 R, ENNReal.ofReal r)=ENNReal.ofReal (R^2/2) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo 0 R) := by
    rw [IntegrableOn,restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp (continuous_id.intervalIntegrable 0 R)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,integral_id]
    simp only [zero_pow (by decide : (2:ℕ)≠0),sub_zero]
  · exact ae_restrict_of_forall_mem measurableSet_Ioo (fun _ hr => hr.1.le)

lemma lintegral_ball_le_of_angular {f : ℂ → ℝ≥0∞} {R : ℝ} (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap 0 r t))≤C) :
    (∫⁻ z in Metric.ball (0:ℂ) R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  by_cases hC : C=⊤
  · simp [hC,ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0<R^2/2)]
  let g := (Metric.ball (0:ℂ) R).indicator f
  rw [← lintegral_indicator measurableSet_ball,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1*g (Complex.polarCoord.symm p))≤_
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans
  calc
    (∫⁻ r in Ioi (0:ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r*g (Complex.polarCoord.symm (r,t)))
      ≤ ∫⁻ r in Ioi (0:ℝ), (Iio R).indicator (fun r => ENNReal.ofReal r*C) r := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases hrR : r<R
        · rw [indicator_of_mem (show r∈Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=f (circleMap 0 r t) := by
            dsimp [g]
            rw [indicator_of_mem,polarCoord_eq_circleMap]
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0<r from hr)] using hrR
          simp_rw [heq]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul' le_rfl (hcircle r ⟨hr,hrR⟩)
        · rw [indicator_of_notMem (show r∉Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=0 := by
            apply indicator_of_notMem
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0<r from hr)] using hrR
          simp only [heq,mul_zero,lintegral_zero,le_refl]
    _ = ∫⁻ r in Ioo 0 R, ENNReal.ofReal r*C := by
      have hset : Iio R∩Ioi (0:ℝ)=Ioo 0 R := by
        ext r
        exact and_comm
      rw [setLIntegral_indicator measurableSet_Iio,hset]
    _ = ENNReal.ofReal (R^2/2)*C := by
      rw [lintegral_mul_const' _ _ hC,lintegral_radius hR.le]

lemma lintegral_ball_center_le_of_angular {f : ℂ → ℝ≥0∞} {c : ℂ} {R : ℝ}
    (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap c r t))≤C) :
    (∫⁻ z in Metric.ball c R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  have heq : (∫⁻ z in Metric.ball c R,f z)=(∫⁻ z in Metric.ball (0:ℂ) R,f (c+z)) := by
    rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self _ c]
    apply lintegral_congr
    intro z
    by_cases hz : z∈Metric.ball (0:ℂ) R
    · rw [indicator_of_mem hz,indicator_of_mem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
    · rw [indicator_of_notMem hz,indicator_of_notMem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  rw [heq]
  apply lintegral_ball_le_of_angular hR
  intro r hr
  simpa only [circleMap,zero_add] using hcircle r hr
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma lintegral_plane_ball_complex (f : Plane → ℝ≥0∞) (a : Plane) (r : ℝ) :
    (∫⁻x in Metric.ball a r,f x)=
      ∫⁻z in Metric.ball (planeComplex a) r,f (planeComplex.symm z) := by
  rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
    ← planeComplex.symm.measurePreserving.lintegral_comp_emb planeComplex.symm.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro z
  have heq : planeComplex.symm z∈Metric.ball a r ↔ z∈Metric.ball (planeComplex a) r := by
    simp only [Metric.mem_ball,← planeComplex.isometry.dist_eq,planeComplex.apply_symm_apply]
  by_cases hz : z∈Metric.ball (planeComplex a) r
  · rw [indicator_of_mem hz,indicator_of_mem (heq.mpr hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (heq.not.mpr hz)]
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem disk_submean {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤
      ENNReal.ofReal (Real.pi*R^2)*(-V a).toENNReal := by
  rw [lintegral_plane_ball_complex]
  have hc : ∀ r∈Ioo 0 R,
      (∫⁻ t in Ioo (-Real.pi) Real.pi,
        (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal)
      ≤ ENNReal.ofReal (2*Real.pi)*(-V a).toENNReal := by
    intro r hr
    have hbr : Metric.closedBall a r⊆Ω := by
      apply Subset.trans _ hball
      intro x hx
      exact lt_of_le_of_lt hx hr.2
    have hs := circle_submean_polar hV hneg htest hr.1 hbr
    rw [polarParameterMeasure,lintegral_smul_measure] at hs
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (2*Real.pi))) hs
    simpa only [smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤2*Real.pi),
      mul_inv_cancel₀ (by positivity : 2*Real.pi≠0),ENNReal.ofReal_one,one_mul] using hh
  apply (lintegral_ball_center_le_of_angular hR hc).trans_eq
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤R^2/2)]
  congr 2
  ring

theorem disk_lintegral_le_of_anchor {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R C : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) (hanchor : (-(C:ℝ):EReal)≤V a) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤ ENNReal.ofReal (Real.pi*R^2)*ENNReal.ofReal C := by
  apply (disk_submean hV hneg htest hR hball).trans
  apply mul_le_mul' le_rfl
  rw [← toENNReal_coe_real]
  apply EReal.toENNReal_le_toENNReal
  simpa only [← EReal.coe_neg,neg_neg] using EReal.neg_le_neg_iff.mpr hanchor

theorem profile_lintegral_D8 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    {a : Plane} (ha : a∈Metric.closedBall 0 1) (hanchor : (-1:EReal)≤V a) :
    (∫⁻x in Metric.ball (0:Plane) 8,(-V x).toENNReal)≤ ENNReal.ofReal (100*Real.pi) := by
  have hsubset : Metric.ball (0:Plane) 8⊆Metric.ball a 10 := by
    intro x hx
    have hd := dist_triangle x 0 a
    have ha' : dist (0:Plane) a≤1 := by simpa only [dist_comm] using Metric.mem_closedBall.mp ha
    change dist x a<10
    change dist x 0<8 at hx
    linarith
  have hball : Metric.ball a 10⊆Metric.ball (0:Plane) 1000 := by
    intro x hx
    have hd := dist_triangle x a 0
    change dist a 0≤1 at ha
    change dist x a<10 at hx
    change dist x 0<1000
    linarith
  apply (lintegral_mono' (Measure.restrict_mono hsubset (le_refl volume)) (le_refl (fun x => (-V x).toENNReal))).trans
  have hh := disk_lintegral_le_of_anchor hV hneg htest (by norm_num : (0:ℝ)<10) hball (C:=1) (by simpa using hanchor)
  simpa only [show Real.pi*(10:ℝ)^2=100*Real.pi by ring,ENNReal.ofReal_one,mul_one] using hh
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma usc_neg_toENNReal_aemeasurable {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) :
    AEMeasurable (fun x => (-V x).toENNReal) (volume.restrict Ω) := by
  apply aemeasurable_restrict_of_measurable_subtype hΩ
  exact EReal.continuous_toENNReal.measurable.comp
    (upperSemicontinuousOn_iff_restrict.mpr hV).measurable.neg

lemma profile_integrable_of_lintegral_ne_top {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (hfin : (∫⁻ x in Ω, (-V x).toENNReal)≠⊤) :
    IntegrableOn (fun x => (V x).toReal) Ω ∧ (∀ᵐx ∂volume.restrict Ω,V x≠⊥) := by
  have hm := usc_neg_toENNReal_aemeasurable hΩ hV
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin
  have heq : (fun x => (V x).toReal)=ᵐ[volume.restrict Ω]
      (fun x => -((-V x).toENNReal.toReal)) := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x hx)),
      EReal.toReal_neg_eq,neg_neg]
  refine ⟨hi.neg.congr heq.symm,?_⟩
  filter_upwards [ae_lt_top' hm hfin] with x hx
  simpa only [EReal.toENNReal_ne_top_iff,ne_eq,EReal.neg_eq_top_iff] using ne_of_lt hx

lemma profile_norm_integral_le {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    {C : ℝ} (hC : 0≤C) (hbound : (∫⁻ x in Ω,(-V x).toENNReal)≤ENNReal.ofReal C) :
    (∫ x in Ω, |(V x).toReal|)≤C := by
  have hfin : (∫⁻ x in Ω,(-V x).toENNReal)≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hi := (profile_integrable_of_lintegral_ne_top hΩ hV hneg hfin).1
  have heq : (fun x => |(V x).toReal|)=ᵐ[volume.restrict Ω]
      (fun x => (-V x).toENNReal.toReal) := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [abs_of_nonpos (EReal.toReal_nonpos (hneg x hx)),
      EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x hx)),EReal.toReal_neg_eq]
  rw [integral_congr_ae heq,integral_toReal (usc_neg_toENNReal_aemeasurable hΩ hV)
    (ae_lt_top' (usc_neg_toENNReal_aemeasurable hΩ hV) hfin)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)
end SharpNodal.Profiles

end
end
end
end
end
end
end

end OAI

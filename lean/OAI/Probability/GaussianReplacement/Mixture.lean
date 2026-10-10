import OAI.Probability.GaussianReplacement.Reference

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


abbrev gaussianVectorPair (d : ℕ) := (stdGaussian (Vector d)).prod (stdGaussian (Vector d))

def sphereCauchyCross {d : ℕ} (e : ℝ) (s t : Sphere d) (x : Vector d×Vector d) : ℝ :=
  regularizedCauchyCross 1 e ⟪(s:Vector d)-(t:Vector d),x.1⟫ ⟪(s:Vector d)-(t:Vector d),x.2⟫

def ownCauchyMixture {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (s : Sphere d)
    (x : Vector d×Vector d) : ℝ := ∫ t, Real.exp (-sphereCauchyCross e s t x) ∂μ

lemma continuous_sphereCauchyCross {d : ℕ} {e : ℝ} (he : 0 < e) (s : Sphere d) :
    Continuous (fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2) := by
  unfold sphereCauchyCross regularizedCauchyCross
  fun_prop (disch := intro z; positivity)

lemma continuous_regularizedReciprocal {d : ℕ} {e : ℝ} (he : 0 < e) (s : Sphere d) :
    Continuous (regularizedReciprocal e s) := by
  unfold regularizedReciprocal
  exact (continuous_const.dist continuous_id |>.max continuous_const).inv₀
    (fun t => (he.trans_le (le_max_right (dist s t) e)).ne')

lemma sphereCauchyCross_lower {d : ℕ} {e : ℝ} (he : 0 < e) (s t : Sphere d)
    (x : Vector d×Vector d) : Real.log Real.pi + Real.log e ≤ sphereCauchyCross e s t x :=
  regularizedCauchyCross_lower he _ _

lemma sphereCauchyCross_norm_integral {d : ℕ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (s t : Sphere d) :
    (∫ x, ‖sphereCauchyCross e s t x‖ ∂gaussianVectorPair d) ≤
      Real.log 2 + cauchyTiltConstant + 2*|Real.log Real.pi+Real.log e| := by
  have hi : Integrable (sphereCauchyCross e s t) (gaussianVectorPair d) :=
    gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he
  have hb := gaussian_regularizedCross_integral ((s:Vector d)-(t:Vector d)) he
  have hdist : ‖(s:Vector d)-(t:Vector d)‖ ≤ 2 := by
    simpa only [dist_eq_norm,Subtype.dist_eq] using sphere_subtype_dist_le_two s t
  have hl := Real.log_le_log (he.trans_le (le_max_right ‖(s:Vector d)-(t:Vector d)‖ e))
    (max_le hdist (by linarith : e ≤ 2))
  have hp (x : Vector d×Vector d) : ‖sphereCauchyCross e s t x‖ ≤
      sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e| := by
    rw [Real.norm_eq_abs,abs_le]
    have hh := sphereCauchyCross_lower he s t x
    constructor <;> linarith [le_abs_self (Real.log Real.pi+Real.log e),neg_abs_le (Real.log Real.pi+Real.log e)]
  have h := integral_mono hi.norm (hi.add (integrable_const _)) hp
  have hv : (∫ x, sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e|
      ∂gaussianVectorPair d) = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
      2*|Real.log Real.pi+Real.log e| := by
    calc
      _ = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
        ∫ (_ : Vector d×Vector d), 2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d :=
          integral_add hi (integrable_const _)
      _ = _ := by simp
  change _ ≤ ∫ x, sphereCauchyCross e s t x + 2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d at h
  rw [hv] at h
  exact h.trans (by dsimp [sphereCauchyCross] at *; linarith)

lemma sphereCauchyCross_joint_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2)
      (μ.prod (gaussianVectorPair d)) := by
  have hm := (continuous_sphereCauchyCross he s).measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he),?_⟩
  apply (integrable_const (Real.log 2+cauchyTiltConstant+2*|Real.log Real.pi+Real.log e|)).mono'
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact sphereCauchyCross_norm_integral he he1 s t

lemma continuous_sphereCauchyCross_slice {d : ℕ} {e : ℝ} (he : 0 < e)
    (s : Sphere d) (x : Vector d×Vector d) : Continuous (fun t => sphereCauchyCross e s t x) := by
  change Continuous ((fun z : Sphere d×(Vector d×Vector d) => sphereCauchyCross e s z.1 z.2) ∘
    (fun t : Sphere d => (t,x)))
  exact (continuous_sphereCauchyCross he s).comp
    (continuous_id.prodMk (continuous_const (y:=x)))

lemma integrable_ownCauchyPDF {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    Integrable (fun t => Real.exp (-sphereCauchyCross e s t x)) μ := by
  have hm : Continuous (fun t => sphereCauchyCross e s t x) :=
    continuous_sphereCauchyCross_slice he s x
  have hme : AEStronglyMeasurable (fun t => Real.exp (-sphereCauchyCross e s t x)) μ :=
    (Real.continuous_exp.comp hm.neg).aestronglyMeasurable
  apply (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e)))).mono' hme
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (neg_le_neg (sphereCauchyCross_lower he s t x)))

lemma ownCauchyMixture_pos {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    0 < ownCauchyMixture μ e s x := by
  apply (integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun t => (Real.exp_pos _).le))
    (integrable_ownCauchyPDF μ he s x)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma ownCauchyMixture_cross_lower {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) (x : Vector d×Vector d) :
    Real.log Real.pi+Real.log e ≤ -Real.log (ownCauchyMixture μ e s x) := by
  have hb : ownCauchyMixture μ e s x ≤ Real.exp (-(Real.log Real.pi+Real.log e)) := by
    have h := integral_mono (integrable_ownCauchyPDF μ he s x)
      (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e))))
      (fun t => Real.exp_le_exp.mpr (neg_le_neg (sphereCauchyCross_lower he s t x)))
    simpa [ownCauchyMixture] using h
  have hl := Real.log_le_log (ownCauchyMixture_pos μ he s x) hb
  rw [Real.log_exp] at hl
  linarith

lemma integrable_weighted_sphereCauchy {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun z : Sphere d×(Vector d×Vector d) => regularizedReciprocal e s z.1 *
      (sphereCauchyCross e s z.1 z.2 + Real.log (regularizedReciprocal e s z.1)))
      (μ.prod (gaussianVectorPair d)) := by
  have hw := continuous_regularizedReciprocal he s
  have hl : Continuous (fun t => Real.log (regularizedReciprocal e s t)) :=
    hw.log (fun t => (regularizedReciprocal_pos he s t).ne')
  have hli : Integrable (fun t => Real.log (regularizedReciprocal e s t)) μ :=
    hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hli' := hli.comp_fst (ν:=gaussianVectorPair d)
  exact ((sphereCauchyCross_joint_integrable μ he he1 s).add hli').bdd_mul
    (hw.comp continuous_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_pos (regularizedReciprocal_pos he s z.1)]
      exact (regularizedReciprocal_bounds he he1 s z.1).2))

lemma ownCauchyMixture_cross_upper {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) (x : Vector d×Vector d) :
    -Real.log (ownCauchyMixture μ e s x) ≤ -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s := by
  have hA : 0 < regularizedScale μ e s := lt_of_lt_of_le (by norm_num) (regularizedScale_bounds μ he he1 s).1
  have hc : Continuous (fun t => sphereCauchyCross e s t x) :=
    continuous_sphereCauchyCross_slice he s x
  have hw := continuous_regularizedReciprocal he s
  have hcw : Continuous (fun t => regularizedReciprocal e s t *
      (-sphereCauchyCross e s t x - Real.log (regularizedReciprocal e s t))) :=
    hw.mul (hc.neg.sub (hw.log (fun t => (regularizedReciprocal_pos he s t).ne')))
  have hi := hcw.integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)
  have h := weighted_log_integral μ (regularizedReciprocal e s)
    (fun t => Real.exp (-sphereCauchyCross e s t x)) (regularizedReciprocal_pos he s)
    (fun t => Real.exp_pos _) (integrable_regularizedReciprocal μ he s)
    (integrable_ownCauchyPDF μ he s x) (by simpa only [Real.log_exp] using hi) hA (ownCauchyMixture_pos μ he s x)
  simp only [Real.log_exp] at h
  have heq : (fun t => regularizedReciprocal e s t * (-sphereCauchyCross e s t x - Real.log (regularizedReciprocal e s t))) =
      fun t => -(regularizedReciprocal e s t * (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t))) := by
    funext t
    ring
  rw [heq,integral_neg] at h
  change -_ ≤ regularizedScale μ e s * (Real.log (ownCauchyMixture μ e s x) - Real.log (regularizedScale μ e s)) at h
  have hh : -Real.log (ownCauchyMixture μ e s x)+Real.log (regularizedScale μ e s) ≤
      (∫ t, regularizedReciprocal e s t * (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s := by
    apply (le_div_iff₀ hA).mpr
    nlinarith
  linarith

lemma ownCauchyMixture_measurable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) : Measurable (ownCauchyMixture μ e s) := by
  have hm : StronglyMeasurable (fun z : Sphere d×(Vector d×Vector d) =>
      Real.exp (-sphereCauchyCross e s z.1 z.2)) :=
    (Real.continuous_exp.comp (continuous_sphereCauchyCross he s).neg).stronglyMeasurable
  exact hm.integral_prod_left'.measurable

lemma ownCauchyMixture_cross_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    Integrable (fun x => -Real.log (ownCauchyMixture μ e s x)) (gaussianVectorPair d) := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  have hu : Integrable (fun x : Vector d×Vector d => -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s)
      (gaussianVectorPair d) := (integrable_const _).add (hi.integral_prod_right.div_const _)
  exact integrable_of_le_of_le (ownCauchyMixture_measurable μ he s).log.neg.aestronglyMeasurable
    (ae_of_all _ (fun x => ownCauchyMixture_cross_lower μ he s x))
    (ae_of_all _ (fun x => ownCauchyMixture_cross_upper μ he he1 s x))
    (integrable_const _) hu

lemma weightedCauchyCross_integral_bound {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, ∫ t, regularizedReciprocal e s t *
      (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ
      ∂gaussianVectorPair d) ≤ regularizedScale μ e s * cauchyTiltConstant := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  rw [←integral_integral_swap hi]
  have hup : Integrable (fun t => regularizedReciprocal e s t * cauchyTiltConstant) μ :=
    (integrable_regularizedReciprocal μ he s).mul_const _
  calc
    _ ≤ ∫ t, regularizedReciprocal e s t * cauchyTiltConstant ∂μ := by
      apply integral_mono hi.integral_prod_left hup
      intro t
      have ht : Integrable (sphereCauchyCross e s t) (gaussianVectorPair d) :=
        gaussian_regularizedCross_integrable ((s:Vector d)-(t:Vector d)) he
      dsimp only
      rw [integral_const_mul]
      have hv : (∫ x, sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)
          ∂gaussianVectorPair d) = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
          Real.log (regularizedReciprocal e s t) := by
        calc
          _ = (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) +
              ∫ (_ : Vector d×Vector d), Real.log (regularizedReciprocal e s t) ∂gaussianVectorPair d :=
            integral_add ht (integrable_const _)
          _ = _ := by simp
      rw [hv]
      apply mul_le_mul_of_nonneg_left _ (regularizedReciprocal_pos he s t).le
      have hb := gaussian_regularizedCross_integral ((s:Vector d)-(t:Vector d)) he
      change (∫ x, sphereCauchyCross e s t x ∂gaussianVectorPair d) ≤ _ at hb
      rw [←dist_eq_norm,←Subtype.dist_eq] at hb
      rw [log_regularizedReciprocal]
      linarith
    _ = _ := integral_mul_const _ _

lemma ownCauchyMixture_cross_integral {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, -Real.log (ownCauchyMixture μ e s x) ∂gaussianVectorPair d) ≤
      cauchyTiltConstant - Real.log (regularizedScale μ e s) := by
  have hi := integrable_weighted_sphereCauchy μ he he1 s
  have hA : 0 < regularizedScale μ e s := lt_of_lt_of_le (by norm_num) (regularizedScale_bounds μ he he1 s).1
  have hu : Integrable (fun x : Vector d×Vector d => -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s)
      (gaussianVectorPair d) := (integrable_const _).add (hi.integral_prod_right.div_const _)
  have hb := integral_mono (ownCauchyMixture_cross_integrable μ he he1 s) hu
    (ownCauchyMixture_cross_upper μ he he1 s)
  have hv : (∫ x, -Real.log (regularizedScale μ e s) +
      (∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ) / regularizedScale μ e s
      ∂gaussianVectorPair d) = -Real.log (regularizedScale μ e s) +
      (∫ x, ∫ t, regularizedReciprocal e s t *
        (sphereCauchyCross e s t x + Real.log (regularizedReciprocal e s t)) ∂μ
        ∂gaussianVectorPair d) / regularizedScale μ e s := by
    rw [integral_add (integrable_const _) (hi.integral_prod_right.div_const _)]
    simp only [integral_const,probReal_univ,one_smul,integral_div]
  rw [hv] at hb
  have hn := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using weightedCauchyCross_integral_bound μ he he1 s)
  linarith



def regularizedCauchyPDF (e a b : ℝ) : ℝ := Real.exp (-regularizedCauchyCross 1 e a b)

lemma regularizedCauchyPDF_eq {e : ℝ} (he : 0 < e) (a b : ℝ) :
    regularizedCauchyPDF e a b = cauchyPDFReal 0
      ⟨Real.sqrt (a^2+e^2), Real.sqrt_nonneg _⟩ b := by
  have hD : 0 < a^2+e^2 := by positivity
  have hT : 0 < b^2+(Real.sqrt (a^2+e^2))^2 := by positivity
  have hs : (⟨Real.sqrt (a^2+e^2),Real.sqrt_nonneg _⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact (Real.sqrt_pos.mpr hD).ne' h'
  have hp := cauchyPDF_pos 0 hs b
  have hl : -regularizedCauchyCross 1 e a b = Real.log (cauchyPDFReal 0
      (⟨Real.sqrt (a^2+e^2),Real.sqrt_nonneg _⟩ : ℝ≥0) b) := by
    change -regularizedCauchyCross 1 e a b = Real.log
      (Real.pi⁻¹ * Real.sqrt (a^2+e^2) * ((b-0)^2+(Real.sqrt (a^2+e^2))^2)⁻¹)
    rw [sub_zero,Real.log_mul (mul_ne_zero (inv_ne_zero Real.pi_ne_zero)
      (Real.sqrt_pos.mpr hD).ne') (inv_ne_zero hT.ne'),
      Real.log_mul (inv_ne_zero Real.pi_ne_zero) (Real.sqrt_pos.mpr hD).ne',Real.log_inv,Real.log_inv,
      Real.log_sqrt hD.le,Real.sq_sqrt hD.le]
    unfold regularizedCauchyCross
    simp only [one_mul]
    rw [show b^2+(a^2+e^2)=a^2+b^2+e^2 by ring]
    ring
  exact (congrArg Real.exp hl).trans (Real.exp_log hp)

lemma integrable_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    Integrable (regularizedCauchyPDF e a) volume := by
  have hf : regularizedCauchyPDF e a = cauchyPDFReal 0
      ⟨Real.sqrt (a^2+e^2), Real.sqrt_nonneg _⟩ := funext (regularizedCauchyPDF_eq he a)
  rw [hf]
  exact integrable_cauchyPDFReal _

lemma integral_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    (∫ b, regularizedCauchyPDF e a b) = 1 := by
  simp_rw [regularizedCauchyPDF_eq he]
  apply integral_cauchyPDFReal_eq_one
  intro h
  have h' := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
  exact (Real.sqrt_pos.mpr (by positivity : 0 < a^2+e^2)).ne' h'

lemma lintegral_regularizedCauchyPDF {e : ℝ} (he : 0 < e) (a : ℝ) :
    (∫⁻ b, ENNReal.ofReal (regularizedCauchyPDF e a b)) = 1 := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_regularizedCauchyPDF he a)
    (ae_of_all _ (fun b => (Real.exp_pos _).le)),integral_regularizedCauchyPDF he]
  simp

def cauchyMixture {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (x : Vector d×Vector d)
    (b : ℝ×ℝ) : ℝ :=
  ∫ t, regularizedCauchyPDF e (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫) ∂μ

lemma cauchyMixture_at_own {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ)
    (s : Sphere d) (x : Vector d×Vector d) :
    cauchyMixture μ e x (⟪(s:Vector d),x.1⟫,⟪(s:Vector d),x.2⟫) = ownCauchyMixture μ e s x := by
  unfold cauchyMixture ownCauchyMixture regularizedCauchyPDF sphereCauchyCross
  simp only [inner_sub_left]

lemma cauchyMixture_integrand_integrable {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b : ℝ×ℝ) :
    Integrable (fun t : Sphere d => regularizedCauchyPDF e
      (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫)) μ := by
  have hm : Measurable (fun t : Sphere d => regularizedCauchyPDF e
      (b.1-⟪(t:Vector d),x.1⟫) (b.2-⟪(t:Vector d),x.2⟫)) := by
    unfold regularizedCauchyPDF regularizedCauchyCross
    fun_prop
  apply (integrable_const (Real.exp (-(Real.log Real.pi+Real.log e)))).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs]
  unfold regularizedCauchyPDF
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (neg_le_neg (regularizedCauchyCross_lower he _ _))

lemma cauchyMixture_pos {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b : ℝ×ℝ) : 0 < cauchyMixture μ e x b := by
  apply (integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun t => (Real.exp_pos _).le))
    (cauchyMixture_integrand_integrable μ he x b)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma cauchyMixture_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : (C×(Vector d×Vector d))×(ℝ×ℝ) => cauchyMixture (κ z.1.1) e z.1.2 z.2) := by
  have hm : StronglyMeasurable (fun z : ((C×(Vector d×Vector d))×(ℝ×ℝ)) × Sphere d =>
      regularizedCauchyPDF e (z.1.2.1-⟪(z.2:Vector d),z.1.1.2.1⟫)
        (z.1.2.2-⟪(z.2:Vector d),z.1.1.2.2⟫)) := by
    apply Measurable.stronglyMeasurable
    unfold regularizedCauchyPDF regularizedCauchyCross
    fun_prop
  exact (hm.integral_kernel_prod_right' (κ:=κ.comap (fun z => z.1.1) (by fun_prop))).measurable

lemma cauchyMixture_normalization {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (x : Vector d×Vector d) (b₁ : ℝ) :
    (∫⁻ b₂, ENNReal.ofReal (cauchyMixture μ e x (b₁,b₂))) = 1 := by
  have hid (b₂ : ℝ) : ENNReal.ofReal (cauchyMixture μ e x (b₁,b₂)) =
      ∫⁻ t : Sphere d, ENNReal.ofReal (regularizedCauchyPDF e
        (b₁-⟪(t:Vector d),x.1⟫) (b₂-⟪(t:Vector d),x.2⟫)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (cauchyMixture_integrand_integrable μ he x (b₁,b₂))
      (ae_of_all _ (fun t => (Real.exp_pos _).le))
  simp_rw [hid]
  rw [lintegral_lintegral_swap (by unfold regularizedCauchyPDF regularizedCauchyCross; fun_prop)]
  have ht (t : Sphere d) : (∫⁻ b₂, ENNReal.ofReal (regularizedCauchyPDF e
      (b₁-⟪(t:Vector d),x.1⟫) (b₂-⟪(t:Vector d),x.2⟫))) = 1 := by
    rw [lintegral_sub_right_eq_self (f:=fun b : ℝ => ENNReal.ofReal
      (regularizedCauchyPDF e (b₁-⟪(t:Vector d),x.1⟫) b))]
    exact lintegral_regularizedCauchyPDF he _
  simp_rw [ht]
  simp



lemma ownCauchyMixture_cross_norm_integral {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    (∫ x, ‖-Real.log (ownCauchyMixture μ e s x)‖ ∂gaussianVectorPair d) ≤
      cauchyTiltConstant - Real.log (1/2:ℝ) + 2*|Real.log Real.pi+Real.log e| := by
  have hi := ownCauchyMixture_cross_integrable μ he he1 s
  have hlo := (regularizedScale_bounds μ he he1 s).1
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo
  have hup := ownCauchyMixture_cross_integral μ he he1 s
  have hb : (∫ x, ‖-Real.log (ownCauchyMixture μ e s x)‖ ∂gaussianVectorPair d) ≤
      (∫ x, -Real.log (ownCauchyMixture μ e s x) ∂gaussianVectorPair d) +
        2*|Real.log Real.pi+Real.log e| := by
    calc
      _ ≤ ∫ x, -Real.log (ownCauchyMixture μ e s x) +
          2*|Real.log Real.pi+Real.log e| ∂gaussianVectorPair d := by
        apply integral_mono hi.norm (hi.add (integrable_const _))
        intro x
        have hx := ownCauchyMixture_cross_lower μ he s x
        dsimp only [Pi.add_apply]
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor <;> linarith [abs_nonneg (Real.log Real.pi+Real.log e),
          neg_abs_le (Real.log Real.pi+Real.log e)]
      _ = _ := by rw [integral_add hi (integrable_const _)]; simp
  linarith

lemma regularizedScale_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : C×Sphere d => regularizedScale (κ z.1) e z.2) := by
  have hm : StronglyMeasurable (fun z : (C×Sphere d)×Sphere d => regularizedReciprocal e z.1.2 z.2) := by
    apply Measurable.stronglyMeasurable
    unfold regularizedReciprocal
    fun_prop
  exact (hm.integral_kernel_prod_right' (κ:=κ.comap Prod.fst measurable_fst)).measurable

lemma ownCauchyMixture_kernel_measurable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] (e : ℝ) :
    Measurable (fun z : (C×Sphere d)×(Vector d×Vector d) => ownCauchyMixture (κ z.1.1) e z.1.2 z.2) := by
  have he : (fun z : (C×Sphere d)×(Vector d×Vector d) => ownCauchyMixture (κ z.1.1) e z.1.2 z.2) =
      (fun z => cauchyMixture (κ z.1.1) e z.1.2 z.2) ∘
        (fun z : (C×Sphere d)×(Vector d×Vector d) => ((z.1.1,z.2),
          (⟪(z.1.2:Vector d),z.2.1⟫,⟪(z.1.2:Vector d),z.2.2⟫))) := by
    funext z
    simp only [Function.comp_apply,cauchyMixture_at_own]
  rw [he]
  exact (cauchyMixture_kernel_measurable κ e).comp (by fun_prop)

lemma ownCauchyMixture_context_integrable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Integrable (fun z : (C×Sphere d)×(Vector d×Vector d) =>
      -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)) (Γ.prod (gaussianVectorPair d)) := by
  have hm := (ownCauchyMixture_kernel_measurable κ e).log.neg
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun z => ownCauchyMixture_cross_integrable (κ z.1) he he1 z.2),?_⟩
  apply (integrable_const (cauchyTiltConstant-Real.log (1/2:ℝ)+2*|Real.log Real.pi+Real.log e|)).mono'
    (hm.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact ownCauchyMixture_cross_norm_integral (κ z.1) he he1 z.2

lemma regularizedScale_context_log_integrable {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Integrable (fun z : C×Sphere d => Real.log (regularizedScale (κ z.1) e z.2)) Γ := by
  apply integrable_of_le_of_le (regularizedScale_kernel_measurable κ e).log.aestronglyMeasurable
    (g₁:=fun _ => Real.log (1/2:ℝ)) (g₂:=fun _ => Real.log e⁻¹)
  · exact ae_of_all _ (fun z => Real.log_le_log (by norm_num) (regularizedScale_bounds (κ z.1) he he1 z.2).1)
  · exact ae_of_all _ (fun z => Real.log_le_log (lt_of_lt_of_le (by norm_num)
      (regularizedScale_bounds (κ z.1) he he1 z.2).1) (regularizedScale_bounds (κ z.1) he he1 z.2).2)
  · exact integrable_const _
  · exact integrable_const _

lemma ownCauchyMixture_context_bound {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    (∫ z : (C×Sphere d)×(Vector d×Vector d), -Real.log (ownCauchyMixture (κ z.1.1) e z.1.2 z.2)
      ∂Γ.prod (gaussianVectorPair d)) ≤
      cauchyTiltConstant - ∫ z : C×Sphere d, Real.log (regularizedScale (κ z.1) e z.2) ∂Γ := by
  have hi := ownCauchyMixture_context_integrable Γ κ he he1
  have hA := regularizedScale_context_log_integrable Γ κ he he1
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ z : C×Sphere d, cauchyTiltConstant - Real.log (regularizedScale (κ z.1) e z.2) ∂Γ :=
      integral_mono hi.integral_prod_left ((integrable_const _).sub hA)
        (fun z => ownCauchyMixture_cross_integral (κ z.1) he he1 z.2)
    _ = _ := by rw [integral_sub (integrable_const _) hA]; simp



lemma reference_gibbs {A : Type*} [MeasurableSpace A]
    (P R Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure R] [SigmaFinite Λ]
    (r q : A → ℝ) (hr : Measurable r) (hq : Measurable q)
    (hrpos : ∀ z, 0 < r z) (hqpos : ∀ z, 0 < q z)
    (hR : Λ.withDensity (fun z => ENNReal.ofReal (r z)) = R)
    (hnorm : (∫⁻ z, ENNReal.ofReal (q z) ∂Λ) = 1)
    (hPR : klDiv P R ≠ ∞) (hri : Integrable (fun z => Real.log (r z)) P)
    (hqi : Integrable (fun z => Real.log (q z)) P) :
    (∫ z, -Real.log (r z) ∂P) - (klDiv P R).toReal ≤ ∫ z, -Real.log (q z) ∂P := by
  let Q := Λ.withDensity (fun z => ENNReal.ofReal (q z))
  let : IsProbabilityMeasure Q := ⟨by simpa only [Q,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using hnorm⟩
  have hd := llr_of_two_densities R Q Λ (fun z => ENNReal.ofReal (r z)) hr.ennreal_ofReal hR
    q hq hqpos rfl
  have hPRac := (klDiv_ne_top_iff.mp hPR).1
  have he : llr R Q =ᵐ[P] fun z => Real.log (r z) - Real.log (q z) := by
    filter_upwards [hPRac.ae_le hd.2] with z hz
    simpa only [ENNReal.toReal_ofReal (hrpos z).le] using hz
  have hi := (hri.sub hqi).congr he.symm
  have hk := klDiv_chain_finite P R Q hPR hd.1 hi
  have hnonneg := ENNReal.toReal_nonneg (a:=klDiv P Q)
  rw [hk.2,integral_congr_ae he,integral_sub hri hqi] at hnonneg
  simp only [integral_neg]
  linarith



end CurrentProjection

end

end OAI

import Mathlib
import OAI.Analysis.RCDHeat.FisherLimit

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: SqrtPairSlope, EntropyMixture, SqrtMixture, MeasureMixture, CouplingMoment. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
 theorem sqrt_pair_increment (a b c d : ℝ) :
    |Real.sqrt (a^2+b^2)-Real.sqrt (c^2+d^2)| ≤ |a-c|+|b-d| := by
  have h := (abs_norm_sub_norm_le (⟨a,b⟩ : ℂ) (⟨c,d⟩ : ℂ)).trans
    (Complex.norm_le_abs_re_add_abs_im ((⟨a,b⟩ : ℂ)-(⟨c,d⟩ : ℂ)))
  simpa only [Complex.norm_def,Complex.normSq_mk,← sq,Complex.sub_re,Complex.sub_im] using h
variable {X : Type*} [MetricSpace X]
 theorem lipschitz_sqrt_pair {f g : X → ℝ} {C D : ℝ≥0}
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) :
    LipschitzWith (C+D) (fun x => Real.sqrt (f x^2+g x^2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  calc
    _ ≤ |f x-f y|+|g x-g y| := sqrt_pair_increment _ _ _ _
    _ ≤ (C:ℝ)*dist x y+(D:ℝ)*dist x y := add_le_add
      (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
      (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
    _ = _ := by rw [NNReal.coe_add,add_mul]
 theorem localSlope_le_sum_of_increment {u f g : X → ℝ} (x : X)
    (h : ∀ y, |u y-u x| ≤ |f y-f x|+|g y-g x|) :
    localSlope u x ≤ localSlope f x+localSlope g x := by
  have hs (r : ℝ) : slopeAtScale u r x ≤ slopeAtScale f r x+slopeAtScale g r x := by
    refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
    have hd := dist_pos.mpr hyx.symm
    calc
      _ ≤ ENNReal.ofReal (|f y-f x|/dist x y+|g y-g x|/dist x y) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← add_div]
        exact div_le_div_of_nonneg_right (h y) hd.le
      _ = ENNReal.ofReal (|f y-f x|/dist x y)+ENNReal.ofReal (|g y-g x|/dist x y) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ _ := add_le_add (slopeAtScale_term_le f hy hyx) (slopeAtScale_term_le g hy hyx)
  apply ENNReal.le_iInf₂_add_iInf₂
  intro r hr s hs'
  calc
    _ ≤ slopeAtScale u (min r s) x :=
      iInf_le_of_le (min r s) (iInf_le_of_le (lt_min hr hs') le_rfl)
    _ ≤ slopeAtScale f (min r s) x+slopeAtScale g (min r s) x := hs _
    _ ≤ _ := add_le_add (slopeAtScale_mono f x (min_le_left _ _))
      (slopeAtScale_mono g x (min_le_right _ _))
 theorem localSlope_sqrt_pair (f g : X → ℝ) (x : X) :
    localSlope (fun y => Real.sqrt (f y^2+g y^2)) x ≤ localSlope f x+localSlope g x :=
  localSlope_le_sum_of_increment x (fun _y => sqrt_pair_increment _ _ _ _)

variable [MeasurableSpace X] (μ : Measure X)
 theorem IsSlopeMajorant.sqrt_pair {f g : X → ℝ} {G H : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ f G) (hH : IsSlopeMajorant μ g H) :
    IsSlopeMajorant μ (fun x => Real.sqrt (f x^2+g x^2)) (G+H) := by
  filter_upwards [hG,hH,Lp.coeFn_add G H] with x hx hy he
  simp only [Pi.add_apply] at he
  rw [he]
  refine ⟨add_nonneg hx.1 hy.1,?_⟩
  exact (localSlope_sqrt_pair f g x).trans
    ((add_le_add hx.2 hy.2).trans_eq (ENNReal.ofReal_add hx.1 hy.1).symm)
end

 
section
open Set Filter MeasureTheory
open scoped Topology
 theorem mul_log_add_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*Real.log a+b*Real.log b ≤ (a+b)*Real.log (a+b) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp
  have hla := Real.log_le_log ha (le_add_of_nonneg_right hb.le)
  have hlb := Real.log_le_log hb (le_add_of_nonneg_left ha.le)
  nlinarith [mul_le_mul_of_nonneg_left hla ha.le,mul_le_mul_of_nonneg_left hlb hb.le]
 theorem mul_log_mul (a b : ℝ) :
    (a*b)*Real.log (a*b) = a*(b*Real.log b)+(a*Real.log a)*b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring
 theorem entropy_mixture_bounds {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*(a*Real.log a)+t*(b*Real.log b)+
        ((1-t)*Real.log (1-t))*a+(t*Real.log t)*b ≤
        ((1-t)*a+t*b)*Real.log ((1-t)*a+t*b) ∧
    ((1-t)*a+t*b)*Real.log ((1-t)*a+t*b) ≤
      (1-t)*(a*Real.log a)+t*(b*Real.log b) := by
  constructor
  · have h := mul_log_add_lower (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht hb)
    rw [mul_log_mul,mul_log_mul] at h
    linarith
  · exact Real.convexOn_mul_log.2 ha hb (sub_nonneg.mpr ht1) ht (by ring)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
 theorem entropy_mixture_integrable {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hef : Integrable (fun x => f x*Real.log (f x)) μ)
    (heg : Integrable (fun x => g x*Real.log (g x)) μ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun x => ((1-t)*f x+t*g x)*Real.log ((1-t)*f x+t*g x)) μ := by
  have hU := (hef.const_mul (1-t)).add (heg.const_mul t)
  have hL := (hU.add (hf.const_mul ((1-t)*Real.log (1-t)))).add (hg.const_mul (t*Real.log t))
  have hm : AEStronglyMeasurable (fun x => ((1-t)*f x+t*g x)*Real.log ((1-t)*f x+t*g x)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable
      ((hf.aestronglyMeasurable.const_mul (1-t)).add (hg.aestronglyMeasurable.const_mul t))
  apply Integrable.mono' (hL.norm.add hU.norm) hm
  filter_upwards [hf0,hg0] with x hx hy
  obtain ⟨hl,hu⟩ := entropy_mixture_bounds hx hy ht ht1
  simp only [Pi.add_apply,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le ((1-t)*(f x*Real.log (f x))+t*(g x*Real.log (g x))+
      ((1-t)*Real.log (1-t))*f x+(t*Real.log t)*g x),
      abs_nonneg ((1-t)*(f x*Real.log (f x))+t*(g x*Real.log (g x)))]
  · linarith [le_abs_self ((1-t)*(f x*Real.log (f x))+t*(g x*Real.log (g x))),
      abs_nonneg ((1-t)*(f x*Real.log (f x))+t*(g x*Real.log (g x))+
      ((1-t)*Real.log (1-t))*f x+(t*Real.log t)*g x)]

 theorem entropy_mixture_integral_bounds {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hef : Integrable (fun x => f x*Real.log (f x)) μ)
    (heg : Integrable (fun x => g x*Real.log (g x)) μ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*(∫x, f x*Real.log (f x) ∂μ)+t*(∫x, g x*Real.log (g x) ∂μ)+
        ((1-t)*Real.log (1-t))*(∫x, f x ∂μ)+(t*Real.log t)*(∫x, g x ∂μ) ≤
      ∫x, ((1-t)*f x+t*g x)*Real.log ((1-t)*f x+t*g x) ∂μ ∧
    (∫x, ((1-t)*f x+t*g x)*Real.log ((1-t)*f x+t*g x) ∂μ) ≤
      (1-t)*(∫x, f x*Real.log (f x) ∂μ)+t*(∫x, g x*Real.log (g x) ∂μ) := by
  have hm := entropy_mixture_integrable μ hf hg hf0 hg0 hef heg ht ht1
  have hU := (hef.const_mul (1-t)).add (heg.const_mul t)
  have hL := (hU.add (hf.const_mul ((1-t)*Real.log (1-t)))).add (hg.const_mul (t*Real.log t))
  have hl := integral_mono_ae hL hm (by
    filter_upwards [hf0,hg0] with x hx hy
    exact (entropy_mixture_bounds hx hy ht ht1).1)
  have hu := integral_mono_ae hm hU (by
    filter_upwards [hf0,hg0] with x hx hy
    exact (entropy_mixture_bounds hx hy ht ht1).2)
  have hI1 := integral_add (hU.add (hf.const_mul ((1-t)*Real.log (1-t)))) (hg.const_mul (t*Real.log t))
  have hI2 := integral_add hU (hf.const_mul ((1-t)*Real.log (1-t)))
  have hI3 := integral_add (hef.const_mul (1-t)) (heg.const_mul t)
  simp only [Pi.add_apply] at hl hu hI1 hI2 hI3
  rw [hI1,hI2,hI3] at hl
  simp only [integral_const_mul] at hl
  rw [hI3] at hu
  simp only [integral_const_mul] at hu
  exact ⟨hl,hu⟩

 theorem entropy_mixture_tendsto {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hef : Integrable (fun x => f x*Real.log (f x)) μ)
    (heg : Integrable (fun x => g x*Real.log (g x)) μ)
    {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (hlim : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun i => ∫x, ((1-t i)*f x+t i*g x)*Real.log ((1-t i)*f x+t i*g x) ∂μ)
      atTop (𝓝 (∫x, f x*Real.log (f x) ∂μ)) := by
  have hUp : Tendsto (fun i => (1-t i)*(∫x, f x*Real.log (f x) ∂μ)+t i*(∫x, g x*Real.log (g x) ∂μ))
      atTop (𝓝 (∫x, f x*Real.log (f x) ∂μ)) := by
    simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub hlim).mul_const _).add (hlim.mul_const _)
  have hLog0 := Real.continuous_mul_log.continuousAt.tendsto.comp hlim
  have hLog1 := Real.continuous_mul_log.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1:ℝ))).sub hlim)
  have hLo : Tendsto (fun i => (1-t i)*(∫x, f x*Real.log (f x) ∂μ)+t i*(∫x, g x*Real.log (g x) ∂μ)+
      ((1-t i)*Real.log (1-t i))*(∫x, f x ∂μ)+(t i*Real.log (t i))*(∫x, g x ∂μ))
      atTop (𝓝 (∫x, f x*Real.log (f x) ∂μ)) := by
    simpa using (hUp.add (hLog1.mul_const _)).add (hLog0.mul_const _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLo hUp
    (fun i => (entropy_mixture_integral_bounds μ hf hg hf0 hg0 hef heg (ht i) (ht1 i)).1)
    (fun i => (entropy_mixture_integral_bounds μ hf hg hf0 hg0 hef heg (ht i) (ht1 i)).2)
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]
noncomputable def sqrtMixture (t : ℝ) (f g : X → ℝ) (x : X) : ℝ :=
  Real.sqrt ((1-t)*f x^2+t*g x^2)
omit [MetricSpace X] in
 theorem sqrtMixture_sq {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (f g : X → ℝ) (x : X) :
    sqrtMixture t f g x^2 = (1-t)*f x^2+t*g x^2 :=
  Real.sq_sqrt (add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg _)) (mul_nonneg ht (sq_nonneg _)))
omit [MetricSpace X] in
 theorem sqrtMixture_eq_pair {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (f g : X → ℝ) :
    sqrtMixture t f g = fun x => Real.sqrt ((Real.sqrt (1-t)*f x)^2+(Real.sqrt t*g x)^2) := by
  funext x
  simp only [sqrtMixture,mul_pow,Real.sq_sqrt ht,Real.sq_sqrt (sub_nonneg.mpr ht1)]
 theorem sqrtMixture_lipschitz {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {f g : X → ℝ} {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g) :
    LipschitzWith (‖Real.sqrt (1-t)‖₊*C+‖Real.sqrt t‖₊*D) (sqrtMixture t f g) := by
  rw [sqrtMixture_eq_pair ht ht1]
  exact lipschitz_sqrt_pair (lipschitzWith_const_mul_real hf _) (lipschitzWith_const_mul_real hg _)
omit [MetricSpace X] in
 theorem sqrtMixture_pos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (f g : X → ℝ)
    (hg : ∀ x, 0 < g x) (x : X) : 0 < sqrtMixture t f g x := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg _))
    (mul_pos ht (sq_pos_of_pos (hg x)))
 theorem sqrtMixture_exp_log_lipschitz (p : X) {b c t R : ℝ} (hb : 0 ≤ b) (hc : 0 < c)
    (ht : 0 < t) (ht1 : t ≤ 1) {f : X → ℝ} {C M : ℝ≥0}
    (hf : LipschitzWith C f) (hfB : ∀ x, |f x| ≤ M)
    (hfS : ∀ x, f x ≠ 0 → dist p x ≤ R) :
    ∃ L : ℝ≥0, LipschitzWith L
      (fun x => Real.log (sqrtMixture t f (fun y => c*Real.exp (-b*dist p y)) x^2)) := by
  have hff : LipschitzWith (M*C+M*C) (fun x => f x^2) := by
    simpa only [pow_two] using lipschitzWith_mul_of_support_bound hf hf hfB (fun x _ => hfB x)
  have hffB (x : X) : |f x^2| ≤ M^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) (hfB x) 2
  have hB (x : X) : |(1-t)*f x^2| ≤ ((‖1-t‖₊*M^2 : ℝ≥0) : ℝ) := by
    simp only [abs_mul,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,NNReal.coe_pow]
    exact mul_le_mul_of_nonneg_left (hffB x) (abs_nonneg _)
  have hS (x : X) (hx : (1-t)*f x^2 ≠ 0) : dist p x ≤ R := by
    apply hfS x
    intro he
    apply hx
    simp [he]
  obtain ⟨L,hL⟩ := positiveTail_log_lipschitz p (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb)
    (mul_pos ht (sq_pos_of_pos hc)) (lipschitzWith_const_mul_real hff (1-t))
    (fun x => mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg _)) hB hS
  refine ⟨L,?_⟩
  convert hL using 1
  funext x
  rw [sqrtMixture_sq ht.le ht1]
  congr 1
  dsimp [positiveTail]
  rw [mul_pow,← Real.exp_nat_mul]
  congr 1
  ring_nf

variable [MeasurableSpace X] (μ : Measure X)
 theorem IsSlopeMajorant.sqrtMixture {f g : X → ℝ} {G H : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ f G) (hH : IsSlopeMajorant μ g H)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsSlopeMajorant μ (sqrtMixture t f g)
      (Real.sqrt (1-t) • G+Real.sqrt t • H) := by
  rw [sqrtMixture_eq_pair ht ht1]
  exact (hG.const_mul μ (Real.sqrt_nonneg _)).sqrt_pair μ (hH.const_mul μ (Real.sqrt_nonneg _))
omit [MetricSpace X] in
 theorem sqrtMixture_majorant_tendsto (G H : Lp ℝ 2 μ) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun i => Real.sqrt (1-t i) • G+Real.sqrt (t i) • H) atTop (𝓝 G) := by
  have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1:ℝ))).sub ht)
  have h0 := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa using (h1.smul_const G).add (h0.smul_const H)
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]
noncomputable def measureMixture (t : ℝ) (ν σ : Measure X) : Measure X :=
  ENNReal.ofReal (1-t) • ν+ENNReal.ofReal t • σ
 theorem measureMixture_probability {ν σ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : IsProbabilityMeasure (measureMixture t ν σ) := by
  constructor
  simp only [measureMixture,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht]
  norm_num
 theorem measureMixture_map {Y : Type*} [MeasurableSpace Y] (t : ℝ) (ν σ : Measure X)
    {f : X → Y} (hf : Measurable f) :
    (measureMixture t ν σ).map f = measureMixture t (ν.map f) (σ.map f) := by
  simp only [measureMixture,Measure.map_add _ _ hf,Measure.map_smul _ hf.aemeasurable]
 theorem measureMixture_self (ν : Measure X) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    measureMixture t ν ν = ν := by
  rw [measureMixture,← add_smul,← ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht]
  norm_num
 theorem measureMixture_integrable {f : X → ℝ} {ν σ : Measure X}
    (hf : Integrable f ν) (hg : Integrable f σ) (t : ℝ) :
    Integrable f (measureMixture t ν σ) := by
  exact integrable_add_measure.mpr ⟨hf.smul_measure ENNReal.ofReal_ne_top,hg.smul_measure ENNReal.ofReal_ne_top⟩
 theorem measureMixture_absolutelyContinuous {μ ν σ : Measure X} (hν : ν ≪ μ) (hσ : σ ≪ μ)
    (t : ℝ) : measureMixture t ν σ ≪ μ := by
  intro s hs
  simp only [measureMixture,Measure.add_apply,Measure.smul_apply,hν hs,hσ hs,smul_zero,add_zero]
 theorem withDensity_mixture (μ : Measure X) {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.withDensity (fun x => ENNReal.ofReal ((1-t)*f x+t*g x)) =
      measureMixture t (μ.withDensity (fun x => ENNReal.ofReal (f x)))
        (μ.withDensity (fun x => ENNReal.ofReal (g x))) := by
  simp_rw [ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ht1) (hf0 _)) (mul_nonneg ht (hg0 _)),
    ENNReal.ofReal_mul (sub_nonneg.mpr ht1),ENNReal.ofReal_mul ht]
  have h1 := withDensity_add_left (μ := μ) (hf.ennreal_ofReal.const_mul (ENNReal.ofReal (1-t)))
    (fun x => ENNReal.ofReal t*ENNReal.ofReal (g x))
  have h2 := withDensity_smul (μ := μ) (ENNReal.ofReal (1-t)) hf.ennreal_ofReal
  have h3 := withDensity_smul (μ := μ) (ENNReal.ofReal t) hg.ennreal_ofReal
  simp only [Pi.add_def,Pi.smul_def,smul_eq_mul] at h1 h2 h3
  rw [h1,h2,h3]
  rfl

variable [MetricSpace X]
 theorem finiteSecondMoment_of_integrable_dist (ν : Measure X) (p : X)
    (h : Integrable (fun x => dist p x^2) ν) : FiniteSecondMoment ν := by
  refine ⟨p,?_⟩
  have he : (fun x => ENNReal.ofReal (dist x p)^2) = fun x => ENNReal.ofReal (dist p x^2) := by
    funext x
    rw [dist_comm,ENNReal.ofReal_pow dist_nonneg]
  rw [he]
  have hnn : 0 ≤ᵐ[ν] (fun x => dist p x^2) := Eventually.of_forall (fun _ => sq_nonneg _)
  exact ((lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable hnn).mpr h).lt_top
 theorem transportCost_mixture (t : ℝ) (π κ : Measure (X×X)) :
    transportCost (measureMixture t π κ) =
      ENNReal.ofReal (1-t)*transportCost π+ENNReal.ofReal t*transportCost κ := by
  simp only [transportCost,measureMixture,lintegral_add_measure,lintegral_smul_measure,smul_eq_mul]
omit [MetricSpace X] in
 theorem mixture_coupling {ν σ η : Measure X} {π κ : Measure (X×X)}
    (hπ₀ : π.map Prod.fst = ν) (hπ₁ : π.map Prod.snd = η)
    (hκ₀ : κ.map Prod.fst = σ) (hκ₁ : κ.map Prod.snd = η)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (measureMixture t π κ).map Prod.fst = measureMixture t ν σ ∧
    (measureMixture t π κ).map Prod.snd = η := by
  rw [measureMixture_map _ _ _ measurable_fst,measureMixture_map _ _ _ measurable_snd,hπ₀,hπ₁,hκ₀,hκ₁,
    measureMixture_self _ ht ht1]
  exact ⟨rfl,rfl⟩
 theorem transportCost_mixture_tendsto (π κ : Measure (X×X))
    (hπ : transportCost π ≠ ∞) (hκ : transportCost κ ≠ ∞)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun i => transportCost (measureMixture (t i) π κ)) atTop (𝓝 (transportCost π)) := by
  simp_rw [transportCost_mixture]
  have h1 := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1:ℝ))).sub ht)
  have h0 := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simpa using (ENNReal.Tendsto.mul_const h1 (Or.inr hπ)).add
    (ENNReal.Tendsto.mul_const h0 (Or.inr hκ))
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
 theorem coupling_dist_sq_integrable {ν σ : Measure X} {π : Measure (X×X)}
    (hπ₀ : π.map Prod.fst = ν) (hπ₁ : π.map Prod.snd = σ) (p : X)
    (h0 : Integrable (fun x => dist p x^2) ν) (h1 : Integrable (fun x => dist p x^2) σ) :
    Integrable (fun xy : X×X => dist xy.1 xy.2^2) π := by
  rw [← hπ₀] at h0
  rw [← hπ₁] at h1
  apply ((h0.comp_measurable measurable_fst).const_mul 2 |>.add
    ((h1.comp_measurable measurable_snd).const_mul 2)).mono'
    (((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable)
  filter_upwards with xy
  simp only [Real.norm_eq_abs,abs_pow,abs_of_nonneg dist_nonneg,Pi.add_apply,Function.comp_apply]
  have hd := dist_triangle xy.1 p xy.2
  rw [dist_comm xy.1 p] at hd
  nlinarith [dist_nonneg (x := xy.1) (y := xy.2),sq_nonneg (dist p xy.1-dist p xy.2)]
 theorem coupling_transportCost_ne_top {ν σ : Measure X} {π : Measure (X×X)}
    (hπ₀ : π.map Prod.fst = ν) (hπ₁ : π.map Prod.snd = σ) (p : X)
    (h0 : Integrable (fun x => dist p x^2) ν) (h1 : Integrable (fun x => dist p x^2) σ) :
    transportCost π ≠ ∞ := by
  have hi := coupling_dist_sq_integrable hπ₀ hπ₁ p h0 h1
  have he : transportCost π = ENNReal.ofReal (∫xy : X×X, dist xy.1 xy.2^2 ∂π) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
    simp only [transportCost,ENNReal.ofReal_pow dist_nonneg]
  rw [he]
  exact ENNReal.ofReal_ne_top
omit [MetricSpace X] [BorelSpace X] [SeparableSpace X] in
 theorem product_coupling (ν σ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] :
    (ν.prod σ).map Prod.fst = ν ∧ (ν.prod σ).map Prod.snd = σ := by
  simp only [Measure.map_fst_prod,Measure.map_snd_prod,measure_univ,one_smul,and_self]

end RegularPointCoordinates

end OAI

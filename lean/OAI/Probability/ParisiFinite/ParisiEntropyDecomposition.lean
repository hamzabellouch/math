import Mathlib
import OAI.Probability.ParisiFinite.ParisiCoshEntropy

namespace OAI

/-! Parisi Entropy Decomposition. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open MeasureTheory ProbabilityTheory Set Real Filter Matrix
open scoped Topology NNReal ContDiff
open MeasureTheory ProbabilityTheory Set Real Filter Matrix
open scoped Topology NNReal
namespace ParisiSpectral

lemma backwardC_entropy_integrable {μ : Measure ℝ} [IsFiniteMeasure μ] {α K a t : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) (ht : a≤t) (hK : 0<K) (d : ℝ) :
    Integrable (fun x => backwardC d K α t x*log (backwardC d K α t x)) (heatLaw μ a t) := by
  have hc := (cosh_ExpGrowth α).integrable_heatLaw ht (by positivity) (by fun_prop) hi
  have hG := (coshEntropy_ExpGrowth α).integrable_heatLaw ht (by positivity) (continuous_coshEntropy α) hi
  have he (x : ℝ) : backwardC d K α t x*log (backwardC d K α t x)=
      ((log K+α^2/2*(d-t))*(K*exp (α^2/2*(d-t))))*cosh (α*x)+
      (K*exp (α^2/2*(d-t)))*coshEntropy α x := by
    rw [backwardC_log d K α t x hK]
    dsimp only [backwardC,coshEntropy]
    ring
  simp_rw [he]
  exact (hc.const_mul _).add (hG.const_mul _)

lemma backwardG_log_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x|) μ) {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    {K : ℝ} (hK : 0<K) (d α t : ℝ) :
    Integrable (fun x => log (backwardC d K α t x)*backwardG d g t x) μ := by
  have hlog := backwardC_log_integrable hi hK d α t
  have hCc : Continuous (fun x => log (backwardC d K α t x)) :=
    (show Continuous (backwardC d K α t) from by unfold backwardC; fun_prop).log
      (fun x => (backwardC_pos hK _ _ _ _).ne')
  have hlog' : Integrable (fun x => log (backwardC d K α t x)) μ :=
    hlog.mono' hCc.aestronglyMeasurable (ae_of_all _ fun x => by simp only [Real.norm_eq_abs]; exact le_rfl)
  exact hlog'.mul_bdd (continuous_heat hc hg.norm_le _).aestronglyMeasurable
    (ae_of_all _ (backwardG_bound hg hc d t))

lemma hankelCPD_entropy_sub_base {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) (hi : Integrable (fun x : ℝ => |x|) μ)
    {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    {a d K α : ℝ} (hK : 0<K) (hgK : g 0<K)
    (hExp : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {s : Set ℝ}
    (hs : ∀ t∈s,a≤t ∧ t≤d) (hsv : Convex ℝ s)
    (hEnt : ∀ t∈s,Integrable (fun x =>
      (backwardC d K α t x-backwardG d g t x)*log (backwardC d K α t x-backwardG d g t x)) (heatLaw μ a t)) :
    HankelCPD (fun t => (∫ x,
      (backwardC d K α t x-backwardG d g t x)*log (backwardC d K α t x-backwardG d g t x) ∂heatLaw μ a t)-
      baseEntropy μ a d K α t) s := by
  have hQ := hankelCPD_linearEntropy (α := α) hμ hi hg hc hK hs hsv
  have hR := (hankelPD_entropyRemainder (α := α) hμ hg hc hK hgK hs hsv).cpd
  apply ((hQ.add hR).sub_const (∫ x,heat (toNNReal (d-a)) g x ∂μ)).congr_on hsv
  intro t ht
  have hiG : Integrable (backwardG d g t) (heatLaw μ a t) :=
    Integrable.of_bound (continuous_heat hc hg.norm_le _).aestronglyMeasurable _
      (ae_of_all _ (backwardG_bound hg hc d t))
  have hiC := backwardC_entropy_integrable hExp (hs t ht).1 hK d
  have hiL := backwardG_log_integrable (heatLaw_firstMoment hi a t) hg hc hK d α t
  have hone : (fun x => (1+log (backwardC d K α t x))*backwardG d g t x)=
      (fun x => backwardG d g t x+log (backwardC d K α t x)*backwardG d g t x) := by
    funext x; ring
  have hneg : (fun x => -log (backwardC d K α t x)*backwardG d g t x)=
      (fun x => -(log (backwardC d K α t x)*backwardG d g t x)) := by funext x; ring
  have hiO : Integrable (fun x => (1+log (backwardC d K α t x))*backwardG d g t x) (heatLaw μ a t) := by
    rw [hone]; exact hiG.add hiL
  have hsplit := integral_add ((hEnt t ht).sub hiC) hiO
  simp only [Pi.sub_apply] at hsplit
  dsimp only
  rw [hneg,integral_neg,hsplit,
    integral_sub (hEnt t ht) hiC,hone,integral_add hiG hiL,
    backwardG_observation_constant hg hc (hs t ht).1 (hs t ht).2,
    baseEntropy_eq_integral hExp (hs t ht).1 hK]
  ring
end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Filter Matrix
open scoped Topology NNReal
namespace ParisiSpectral

lemma PositiveOnPD.heat_antitone {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : PositiveOnPD μ)
    {f : ℝ → ℝ} (hf : PositiveDefinite f) (hc : Continuous f) {s t : ℝ≥0} (hst : s≤t) :
    (∫ x,heat t f x ∂μ)≤∫ x,heat s f x ∂μ := by
  have hh := hμ.heat_le (hf.heat hc s) (continuous_heat hc hf.norm_le s) (t-s)
  rw [heat_heat hc hf.norm_le,tsub_add_cancel_of_le hst] at hh
  exact hh

lemma PositiveOnPD.heatObservation_antitone {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) {f : ℝ → ℝ} (hf : PositiveDefinite f) (hc : Continuous f)
    {a x y : ℝ} (hax : a≤x) (hxy : x≤y) : heatObservation μ a f y≤heatObservation μ a f x := by
  have hi (t : ℝ) : Integrable f (heatLaw μ a t) :=
    Integrable.of_bound hc.aestronglyMeasurable _ (ae_of_all _ hf.norm_le)
  rw [heatObservation_eq_integral (hax.trans hxy) hc,heatObservation_eq_integral hax hc,
    integral_heatLaw (hi y),integral_heatLaw (hi x)]
  exact hμ.heat_antitone hf hc (toNNReal_le_toNNReal (by linarith))

lemma hankelPD_heatObservation {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) {f : ℝ → ℝ} (hf : PositiveDefinite f) (hc : Continuous f)
    {a : ℝ} {s : Set ℝ} (hs : ∀ t∈s,a≤t) (hsv : Convex ℝ s) :
    HankelPD (heatObservation μ a f) s := by
  have hh := hankelPD_heatLaw hμ hs hsv (F := fun _ => f) (fun _ _ => hc)
    (hf.submatrix (fun p : s × ℝ => p.2))
  have hmid (x y : s) : ((x:ℝ)+y)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]
      using hsv.midpoint_mem x.property y.property
  change (Matrix.of (fun x y : s => heatObservation μ a f ((x+y)/2))).PosSemidef
  have he : Matrix.of (fun x y : s => heatObservation μ a f ((x+y)/2))=
      Matrix.of (fun x y : s => ∫ z,f z ∂heatLaw μ a ((x+y)/2)) := by
    ext x y
    simp only [Matrix.of_apply,heatObservation_eq_integral (hs _ (hmid x y)) hc]
  rw [he]
  exact hh

lemma heatObservation_pos {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ] {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x,0<f x) {C : ℝ} (hb : ∀ x,‖f x‖≤C) (a t : ℝ) :
    0<heatObservation μ a f t := by
  have hi : Integrable (fun p : ℝ × ℝ => f (p.1+sqrt (t-a)*p.2)) (μ.prod (gaussianReal 0 1)) :=
    Integrable.of_bound (by fun_prop) C (ae_of_all _ fun p => hb _)
  rw [heatObservation,integral_pos_iff_support_of_nonneg (fun p => (hp _).le) hi]
  have hs : Function.support (fun p : ℝ × ℝ => f (p.1+sqrt (t-a)*p.2))=univ := by
    ext p
    simp [Function.mem_support,(hp _).ne']
  rw [hs]
  rw [←univ_prod_univ,Measure.prod_prod,show (gaussianReal 0 1) univ=1 from measure_univ,mul_one]
  exact Measure.measure_univ_pos.mpr (NeZero.ne μ)

lemma sechCube_PD (α : ℝ) : PositiveDefinite (fun x => (cosh (α*x))⁻¹^3) := by
  have hh := cosh_neg_rpow_positiveDefinite (show (0:ℝ)<3 by norm_num) α
  have he (x : ℝ) : cosh (α*x)^(-(3:ℝ))=(cosh (α*x))⁻¹^3 := by
    rw [rpow_neg (cosh_pos _).le,show (3:ℝ)=(3:ℕ) by norm_num,rpow_natCast,inv_pow]
  simpa only [he] using hh
lemma continuous_sechCube (α : ℝ) : Continuous (fun x => (cosh (α*x))⁻¹^3) :=
  ((continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀ (fun _ => (cosh_pos _).ne')).pow 3

lemma hankelPD_baseCurvature {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) {a d K α : ℝ} (hK : 0≤K) {s : Set ℝ}
    (hs : ∀ t∈s,a≤t) (hsv : Convex ℝ s) :
    HankelPD (baseCurvature μ a d K α) s := by
  have hh := hankelPD_heatObservation hμ (sechCube_PD α) (continuous_sechCube α) hs hsv
  have hw := (posSemidef_weight hh (fun t : s => exp (α^2/4*(d-t)))).smul
    (show 0≤α^4/2*K by positivity)
  have he : Matrix.of (fun x y : s => baseCurvature μ a d K α ((x+y)/2))=
      (α^4/2*K) • Matrix.of (fun x y : s => exp (α^2/4*(d-x))*exp (α^2/4*(d-y))*
        heatObservation μ a (fun z => (cosh (α*z))⁻¹^3) ((x+y)/2)) := by
    ext x y
    simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,baseCurvature,weightedHeat,←exp_add]
    rw [show α^2/4*(d-(x:ℝ))+α^2/4*(d-(y:ℝ))=α^2/2*(d-((x:ℝ)+y)/2) by ring]
    ring
  change (Matrix.of (fun x y : s => baseCurvature μ a d K α ((x+y)/2))).PosSemidef
  rw [he]
  exact hw

lemma baseCurvature_strictAnti {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ]
    (hμ : PositiveOnPD μ) {a d K α : ℝ} (hK : 0<K) (hα : α≠0)
    {x y : ℝ} (hax : a≤x) (hxy : x<y) : baseCurvature μ a d K α y<baseCurvature μ a d K α x := by
  have hp := heatObservation_pos (μ := μ) (continuous_sechCube α)
    (fun z => by positivity : ∀ z,0<(cosh (α*z))⁻¹^3) (sechCube_PD α).norm_le a x
  have hle := hμ.heatObservation_antitone (sechCube_PD α) (continuous_sechCube α) hax hxy.le
  have hn := heatObservation_pos (μ := μ) (continuous_sechCube α)
    (fun z => by positivity : ∀ z,0<(cosh (α*z))⁻¹^3) (sechCube_PD α).norm_le a y
  have he : exp (α^2/2*(d-y))<exp (α^2/2*(d-x)) := by
    apply exp_lt_exp.mpr
    nlinarith [sq_pos_of_ne_zero hα]
  have hh := mul_lt_mul_of_pos_right he hn
  have hh' := mul_le_mul_of_nonneg_left hle (exp_pos (α^2/2*(d-x))).le
  have hv := mul_lt_mul_of_pos_left (hh.trans_le hh') (show 0<α^4/2*K by positivity)
  simpa only [baseCurvature,weightedHeat,mul_assoc] using hv

lemma baseCurvature_midpoint_lt {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ]
    (hμ : PositiveOnPD μ) {a d K α : ℝ} (hK : 0<K) (hα : α≠0)
    {x y : ℝ} (hax : a≤x) (hxy : x<y) :
    2*baseCurvature μ a d K α ((x+y)/2)<baseCurvature μ a d K α x+baseCurvature μ a d K α y := by
  exact (hankelPD_baseCurvature hμ hK.le (s := Ici a) (fun t ht => ht) (convex_Ici a)).midpoint_lt
    hax (hax.trans hxy.le) (baseCurvature_strictAnti hμ hK hα hax hxy).ne'
end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

 

lemma expectedSquareCurvature_strict_midpoint (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : 0<a) (had : a<d)
    (hd1 : d<1) (hα : 0<α) (hc : ∀ u∈Icc a d,c.val u=α)
    {x y : ℝ} (hx : x∈Ioo (a:ℝ) d) (hy : y∈Ioo (a:ℝ) d) (hxy : x<y) :
    2*c.expectedSquareCurvature P W hβ ((x+y)/2)<
      c.expectedSquareCurvature P W hβ x+c.expectedSquareCurvature P W hβ y := by
  let A : Time := ⟨a,a.coe_nonneg,by exact_mod_cast (had.le.trans hd1.le)⟩
  let μ : Measure ℝ := c.conjugateMeasure P W hβ A
  have hca : c.val ⟨A,A.property.1⟩=α := hc a ⟨le_rfl,had.le⟩
  have hca0 : 0<c.val ⟨A,A.property.1⟩ := by rw [hca]; exact hα
  have : IsFiniteMeasure μ := c.conjugateMeasure_finite hβ hW A hca0
  have : NeZero μ := ⟨c.conjugateMeasure_ne_zero hβ hW A⟩
  have hμ : PositiveOnPD μ := c.conjugateMeasure_positive hβ hW A (by exact_mod_cast ha0) hca0
  have hi : Integrable (fun z : ℝ => |z|) μ := c.conjugateMeasure_firstMoment hβ hW A hca0
  have hExp : Integrable (fun z => exp ((|(α:ℝ)|+1)*|z|)) μ :=
    c.conjugateMeasure_exp_abs hβ hW A hca0 (by positivity)
  obtain ⟨K,g,hK,hg,hgc,hgK,he⟩ := c.plateau_backward_representation hβ had hd1.le hα hc
  have hActual (t : ℝ) (ht : t∈Ioo (a:ℝ) d) :
      Integrable (fun z => (backwardC d K α t z-backwardG d g t z)*
        log (backwardC d K α t z-backwardG d g t z)) (heatLaw μ a t) ∧
      c.fieldEntropy hβ P W α t=(∫ z,(backwardC d K α t z-backwardG d g t z)*
        log (backwardC d K α t z-backwardG d g t z) ∂heatLaw μ a t) := by
    have ht0 : 0<t := (show (0:ℝ)<a by exact_mod_cast ha0).trans ht.1
    have ht1 : t<1 := ht.2.trans (by exact_mod_cast hd1)
    let T : Time := ⟨t,ht0.le,ht1.le⟩
    let n : ℝ≥0 := ⟨t,ht0.le⟩
    have hn : n∈Ioo a d := ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
    have hct : c.val ⟨T,T.property.1⟩=α := hc n ⟨hn.1.le,hn.2.le⟩
    have hl := c.conjugateMeasure_eq_heatLaw hβ hW ha0.ne' hd1.le hα hc (t := n) ⟨hn.1,hn.2.le⟩
    change c.conjugateMeasure P W hβ T=heatLaw μ a t at hl
    have hei (z : ℝ) : exp ((α:ℝ)*field β c.val ⟨T,T.property.1⟩ z)=
        backwardC d K α t z-backwardG d g t z := he n ⟨hn.1.le,hn.2⟩ z
    have hint := c.conjugateMeasure_entropy_integrable hβ hW T
    rw [hct,hl] at hint
    simp_rw [hei] at hint
    have heq := c.fieldEntropy_eq hβ hW T ht0 ht1 hct
    rw [hl] at heq
    simp_rw [hei] at heq
    exact ⟨hint,heq⟩
  have hS : HankelCPD (fun t => c.fieldEntropy hβ P W α t-baseEntropy μ a d K α t) (Ioo (a:ℝ) d) := by
    have hh := hankelCPD_entropy_sub_base hμ hi hg hgc hK hgK hExp
      (fun t (ht : t∈Ioo (a:ℝ) d) => ⟨ht.1.le,ht.2.le⟩) (convex_Ioo (a:ℝ) d)
      (fun t ht => (hActual t ht).1)
    exact hh.congr_on (convex_Ioo (a:ℝ) d) (fun t ht => by dsimp only; rw [(hActual t ht).2])
  have hD : HankelPD (fun t => (α:ℝ)^2/2*c.expectedSquareCurvature P W hβ t-baseCurvature μ a d K α t)
      (Ioo (a:ℝ) d) := by
    apply hS.has_second_derivative (convex_Ioo (a:ℝ) d) isOpen_Ioo
      (nonempty_Ioo.mpr (by exact_mod_cast had))
      (f' := fun t => (α:ℝ)^2/2*expectedProduct P W c c (c.driftData hβ) t-baseEntropyD μ a d K α t)
    · intro t ht
      exact (c.fieldEntropy_hasDerivAt hβ hW hc ht).sub (baseEntropy_hasDerivAt hExp ht.1 d K)
    · intro t ht
      exact (c.fieldEntropyD_hasDerivAt hβ hW α
        ⟨lt_of_le_of_lt a.coe_nonneg ht.1,ht.2.trans (by exact_mod_cast hd1)⟩).sub
        (baseEntropyD_hasDerivAt hExp ht.1 d K)
    · exact ((continuous_const.mul (c.expectedSquareCurvature_continuous hW hβ)).sub
        (continuous_baseCurvature hExp a d K)).continuousOn
  have hmid := hD.midpoint_le hx hy
  have hbase := baseCurvature_midpoint_lt (α := (α:ℝ)) (d := (d:ℝ)) hμ hK (by exact_mod_cast hα.ne') hx.1.le hxy
  have ha : 0<(α:ℝ)^2/2 := by positivity
  nlinarith
end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiSpectral
lemma not_isLocalMax_of_strict_midpoint {f : ℝ → ℝ} {a d t : ℝ}
    (ht : t∈Ioo a d)
    (hf : ∀ x∈Ioo a d,∀ y∈Ioo a d,x<y → 2*f ((x+y)/2)<f x+f y) :
    ¬IsLocalMax f t := by
  intro hmax
  have hopen : ∀ᶠ u in 𝓝 t,u∈Ioo a d := isOpen_Ioo.mem_nhds ht
  have hh : ∀ᶠ u in 𝓝 t,u∈Ioo a d ∧ f u≤f t := hopen.and hmax
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hh
  have hxm : t-ε/2∈Metric.ball t ε := by
    rw [Metric.mem_ball,Real.dist_eq,show t-ε/2-t= -(ε/2) by ring,abs_neg,abs_of_pos (by positivity : 0<ε/2)]
    linarith
  have hym : t+ε/2∈Metric.ball t ε := by
    rw [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity : 0<ε/2)]
    linarith
  have hx := hball hxm
  have hy := hball hym
  have hm := hf (t-ε/2) hx.1 (t+ε/2) hy.1 (by linarith)
  rw [show (t-ε/2+(t+ε/2))/2=t by ring] at hm
  linarith [hx.2,hy.2]
end ParisiSpectral
namespace ParisiFinite.BoundedCoefficient
open ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
lemma expectedSquareCurvature_not_isLocalMax (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : 0<a) (had : a<d)
    (hd1 : d<1) (hα : 0<α) (hc : ∀ u∈Icc a d,c.val u=α)
    {t : ℝ} (ht : t∈Ioo (a:ℝ) d) :
    ¬IsLocalMax (c.expectedSquareCurvature P W hβ) t := by
  exact not_isLocalMax_of_strict_midpoint ht (fun x hx y hy hxy =>
    c.expectedSquareCurvature_strict_midpoint hβ hW ha0 had hd1 hα hc hx hy hxy)
end ParisiFinite.BoundedCoefficient
namespace ParisiFinite
open BoundedCoefficient
 

theorem full_support_minimizer {β : ℝ≥0} (hβ : (1:ℝ)<β)
    (ρ : ProbabilityMeasure OrderPoint) (hρ : IsMinimizingParisiMeasure β ρ) :
    ∃ q : OrderPoint,0<(q:ℝ) ∧ (q:ℝ)<1 ∧ (ρ:Measure OrderPoint).support=Iic q := by
  by_contra hne
  obtain ⟨hbp,a,b,α,t,ha,hb,hab,hb1,hα,hg,hc,ht,hft,hmax⟩ :=
    minimizingParisi_positive_plateau_localMax_countercase hβ hρ hne
  have ht0 : 0<t := lt_of_le_of_lt a.property.1 ht.1
  have han : 0≤(a:ℝ) := a.property.1
  have hbn : 0≤(b:ℝ) := b.property.1
  let A : ℝ≥0 := ⟨((a:ℝ)+t)/2,by positivity⟩
  let D : ℝ≥0 := ⟨((b:ℝ)+t)/2,by positivity⟩
  have ha0 : 0<A := by change (0:ℝ)<((a:ℝ)+t)/2; positivity
  have had : A<D := by change ((a:ℝ)+t)/2<((b:ℝ)+t)/2; have hab' : (a:ℝ)<b := hab; linarith
  have hd1 : D<1 := by change ((b:ℝ)+t)/2<1; linarith [ht.2]
  have htAD : t∈Ioo (A:ℝ) D := by change ((a:ℝ)+t)/2<t ∧ t<((b:ℝ)+t)/2; constructor <;> linarith [ht.1,ht.2]
  have hcoef : ∀ u∈Icc A D,(ofMeasure β ρ).val u=α := by
    intro u hu
    apply hc
    · have hu' : ((a:ℝ)+t)/2≤u := hu.1
      linarith [ht.1]
    · have hu' : (u:ℝ)≤((b:ℝ)+t)/2 := hu.2
      linarith [ht.2]
  exact (ofMeasure β ρ).expectedSquareCurvature_not_isLocalMax hbp
    BrownianConstruction.brownianMotion_isBrownian ha0 had hd1 hα hcoef htAD hmax
end ParisiFinite

end

end OAI

import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNodes
import OAI.Probability.LogConcave.Complexity.TerminalDerivativeBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def ordinaryDerivativeWeight (u : I → ℝ) (a b : ℝ) (i : I) : ℝ :=
  ∫t in a..b,(b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))

lemma inv_intervalIntegrable {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact continuousOn_id.inv₀ (fun t ht => ne_of_gt (ha.trans_le ht.1))

lemma ordinaryDerivativeWeight_integrand_continuousOn (u : I → ℝ) (a b : ℝ) (i : I)
    (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun t => (b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_const.mul (continuousOn_id.inv₀
    (fun t ht => ne_of_gt (ha.trans_le ht.1)))).mul
      ((basisDerivative_continuous u i).comp
        ((continuous_id.sub continuous_const).div_const _)).continuousOn

lemma ordinaryDerivativeWeight_integral (u : I → ℝ) (v : I → E) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    (∫t in a..b,t⁻¹ • ((b-a)⁻¹ • derivativeInterpolation u v ((t-a)/(b-a))))=
      ∑i,ordinaryDerivativeWeight u a b i • v i := by
  simp only [derivativeInterpolation,Finset.smul_sum,smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    unfold ordinaryDerivativeWeight
    rw [←intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr
    intro t _
    module
  · intro i _
    have hh := ((ordinaryDerivativeWeight_integrand_continuousOn u a b i ha hab).smul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => v i) (uIcc a b))).intervalIntegrable (μ:=volume)
    convert hh using 1
    funext t
    congr 1
    ring

omit [CompleteSpace E] in
lemma derivativeInterpolation_joint_continuous {Ω : Type*} [TopologicalSpace Ω]
    (u : I → ℝ) (v : I → Ω → E) (hv : ∀i,Continuous (v i)) :
    Continuous (fun p : ℝ × Ω => derivativeInterpolation u (fun i => v i p.2) p.1) := by
  exact continuous_finsetSum _ (fun i _ =>
    ((basisDerivative_continuous u i).comp continuous_fst).smul ((hv i).comp continuous_snd))

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω] {μ : Measure Ω} [SFinite μ]

lemma ordinaryDerivativeWeight_error_rms (u : I → ℝ) (f g : ℝ × Ω → E)
    (hf : Continuous f) (hg : Continuous g) {a b B : ℝ}
    (ha : 0<a) (hab : a<b) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) 1,Integrable (fun z =>
      ‖g (a+(b-a)*t,z)-(b-a)⁻¹ • derivativeInterpolation u (fun i => f (a+(b-a)*u i,z)) t‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) 1,(∫z,
      ‖g (a+(b-a)*t,z)-(b-a)⁻¹ • derivativeInterpolation u (fun i => f (a+(b-a)*u i,z)) t‖^2 ∂μ)≤B) :
    let err := fun z => (∫t in a..b,t⁻¹ • g (t,z))-
      ∑i,ordinaryDerivativeWeight u a b i • f (a+(b-a)*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤((b-a)/a)^2*B := by
  dsimp only
  let η := volume.restrict (Ioc a b)
  let R := fun p : ℝ × Ω => g p-(b-a)⁻¹ • derivativeInterpolation u
    (fun i => f (a+(b-a)*u i,p.2)) ((p.1-a)/(b-a))
  have hRc : Continuous R := hg.sub
    (((derivativeInterpolation_joint_continuous u (fun i z => f (a+(b-a)*u i,z))
      (fun i => hf.comp (continuous_const.prodMk continuous_id))).comp
        (((continuous_fst.sub continuous_const).div_const _).prodMk continuous_snd)).const_smul _)
  have hrange {t : ℝ} (ht : t∈Ioc a b) : (t-a)/(b-a)∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1.le) (sub_pos.mpr hab).le
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
  have hcoord (t : ℝ) : a+(b-a)*((t-a)/(b-a))=t := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have hri : ∀ᵐ t ∂η,Integrable (fun z => ‖R (t,z)‖^2) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [R,hcoord] using hi _ (hrange ht)
  have hrB : ∀ᵐ t ∂η,(∫z,‖R (t,z)‖^2 ∂μ)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [R,hcoord] using hB _ (hrange ht)
  have hw : AEStronglyMeasurable (fun t : ℝ => t⁻¹) η := measurable_id.inv.aestronglyMeasurable
  have hwb : ∀ᵐ t ∂η,|t⁻¹|≤a⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [abs_of_nonneg (inv_nonneg.mpr (ha.trans ht.1).le)]
    exact inv_anti₀ ha ht.1.le
  have hv := RMSIntegral.weighted_time_seed hRc.aestronglyMeasurable hw hB0 hwb hri hrB
  have hη : η.real univ=b-a := by
    dsimp only [η,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hab.le
  have he (z : Ω) : (∫t in a..b,t⁻¹ • g (t,z))-
      ∑i,ordinaryDerivativeWeight u a b i • f (a+(b-a)*u i,z)=
        ∫t,t⁻¹ • R (t,z) ∂η := by
    rw [←ordinaryDerivativeWeight_integral u _ ha hab.le]
    have hg' : IntervalIntegrable (fun t => t⁻¹ • g (t,z)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab.le]
      exact (continuousOn_id.inv₀ (fun t ht => ne_of_gt (ha.trans_le ht.1))).smul
        (hg.comp (continuous_id.prodMk continuous_const)).continuousOn
    have hp' : IntervalIntegrable (fun t => t⁻¹ • ((b-a)⁻¹ • derivativeInterpolation u
        (fun i => f (a+(b-a)*u i,z)) ((t-a)/(b-a)))) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab.le]
      apply (continuousOn_id.inv₀ (fun t ht => ne_of_gt (ha.trans_le ht.1))).smul
      apply Continuous.continuousOn
      apply Continuous.const_smul
      exact (derivativeInterpolation_joint_continuous u (fun i (_ : Unit) => f (a+(b-a)*u i,z))
        (fun _ => continuous_const)).comp
          (((continuous_id.sub continuous_const).div_const _).prodMk
            (continuous_const : Continuous (fun _ : ℝ => ())))
    rw [←intervalIntegral.integral_sub hg' hp',intervalIntegral.integral_of_le hab.le]
    congr 1
    funext t
    exact (smul_sub _ _ _).symm
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hη]
  ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

def terminalQuadratureWeight (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h (n+1)) : ℝ :=
  if i.1.val=0 then
    zeroHermiteWeight (probabilityNodes (n+1)) 0 i.2/probabilityCellLength T h i.1
  else ordinaryDerivativeWeight (probabilityNodes (n+1))
    (logMeshNode T h i.1.val) (logMeshNode T h (i.1.val+1)) i.2

lemma probabilityNodes_zero (n : ℕ) : probabilityNodes n 0=0 := by
  simp [probabilityNodes]

lemma logMeshNode_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {j : ℕ} (hj : 0<j) : 0<logMeshNode T h j := by
  simpa only [logMeshNode_zero] using logMeshNode_strictMono hT0 hT1 hh hj

lemma probabilityCellLength_le_h {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (i : Fin (logMeshCount T h)) : probabilityCellLength T h i≤h := by
  have he := logMeshCell_upper hT0 hT1 hh i.val
  have ha := (logMeshNode_mem hT0 hT1 hh i.2.le).1
  dsimp only [probabilityCellLength]
  nlinarith

lemma logMeshFirst_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hs : h≤Real.log 2) : h/4≤logMeshNode T h 1 := by
  simpa only [logMeshNode_zero,zero_add,sub_zero,mul_one] using
    logMeshCell_lower hT0 hT1 hh hL hs 0

lemma probabilityCellLength_ratio {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hs : h≤Real.log 2)
    (i : Fin (logMeshCount T h)) (hi : i.val≠0) :
    probabilityCellLength T h i/logMeshNode T h i.val≤4 := by
  have ha := logMeshFirst_lower hT0 hT1 hh hL hs
  have hm : logMeshNode T h 1≤logMeshNode T h i.val :=
    (logMeshNode_strictMono hT0 hT1 hh).monotone (Nat.one_le_iff_ne_zero.mpr hi)
  have hp := logMeshNode_pos hT0 hT1 hh (Nat.pos_of_ne_zero hi)
  rw [div_le_iff₀ hp]
  have hc := probabilityCellLength_le_h hT0 hT1 hh i
  linarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma regularized_intervalIntegrable_nonneg {f : ℝ → E} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (h0 : f 0=0)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume a b := by
  have hc : Continuous (dslope f 0) := continuousOn_univ.mp
    ((continuousOn_dslope (s:=univ) (by simp)).mpr ⟨hf.continuousOn,hd⟩)
  apply (hc.intervalIntegrable a b).congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  simp only [dslope_of_ne f (ne_of_gt (ha.trans_lt ht.1)),slope_def_module,h0,sub_zero]

lemma regularized_integral_scale (f : ℝ → E) {b : ℝ} (hb : b≠0) :
    (∫t in (0:ℝ)..b,t⁻¹ • f t)=(∫t in (0:ℝ)..1,t⁻¹ • f (b*t)) := by
  have he := intervalIntegral.smul_integral_comp_mul_left (a:=0) (b:=1)
    (fun t => t⁻¹ • f t) b
  simp only [mul_zero,mul_one] at he
  rw [←he,←intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [smul_smul,mul_inv_rev]
  congr 1
  field_simp

end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_cell_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T)
    (c : Fin (logMeshCount T h)) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
    let err := fun z => (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
      ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤32*(1+D^2+H^2)*
        (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
  let A := (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d
  let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
  have hA : 0≤A := by dsimp only [A]; positivity
  have ha := logMeshNode_mem hT0 hT1 hh c.2.le
  have hb := logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)
  have hab := logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self c.val)
  have hc := logMeshCell_upper_right hT0 hT1 hh hs c.val
  by_cases hc0 : c.val=0
  · have hb0 := logMeshNode_pos hT0 hT1 hh (by omega : 0<c.val+1)
    have hv := terminal_hermite_cell_rms hF x hr hlam hl hT0 hT1
      (probabilityNodes (n+1)) (probabilityNodes_injective (by omega)) 0
      (probabilityNodes_zero _) (probabilityNodes_mem (by omega)) n (by simp) hd
      hb0 hb.2 (by positivity : 0≤2*h) (by simpa only [hc0,logMeshNode_zero,sub_zero] using hc)
    dsimp only at hv
    have hEq (z : Point d × Point d) :
        (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
          ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)=
        (∫t in (0:ℝ)..1,t⁻¹ • J 1 (logMeshNode T h (c.val+1)*t,z))-
          ∑i,(zeroHermiteWeight (probabilityNodes (n+1)) 0 i/logMeshNode T h (c.val+1)) •
            J 0 (logMeshNode T h (c.val+1)*probabilityNodes (n+1) i,z) := by
      simp only [terminalQuadratureWeight,probabilityNodeTime,probabilityCellLength,
        hc0,ite_true,logMeshNode_zero,sub_zero,zero_add]
      rw [regularized_integral_scale _ (ne_of_gt (logMeshNode_pos hT0 hT1 hh (by omega : 0<1)))]
    dsimp only [J] at hEq
    simp_rw [hEq]
    refine ⟨hv.1,hv.2.trans ?_⟩
    have he : 2*(1+H^2)≤32*(1+D^2+H^2) := by nlinarith [sq_nonneg D,sq_nonneg H]
    convert mul_le_mul_of_nonneg_right he hA using 1 <;> ring
  · have ha0 := logMeshNode_pos hT0 hT1 hh (by omega : 0<c.val)
    have hv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
      terminal_derivative_cell_rms hF x hr hlam hl hT0 hT1
        (probabilityNodes (n+1)) (probabilityNodes_injective (by omega))
        (probabilityNodes_mem (by omega)) n (by simp) hd ha.1 hab hb.2
        (by positivity : 0≤2*h) hc ht
    have hi (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := (hv t ht).1
    have hB (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        (∫z,‖J 1 (logMeshNode T h c.val+probabilityCellLength T h c*t,z)-
          (probabilityCellLength T h c)⁻¹ • derivativeInterpolation (probabilityNodes (n+1))
            (fun i => J 0 (logMeshNode T h c.val+probabilityCellLength T h c*probabilityNodes (n+1) i,z)) t‖^2 ∂μ)
          ≤2*(1+D^2)*A := by
      apply (hv t ht).2.trans
      have hps := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => abs_nonneg
        (basisDerivative (probabilityNodes (n+1)) i t))) (hDu t ht) 2
      have he : 2*(1+(∑i,|basisDerivative (probabilityNodes (n+1)) i t|)^2)≤2*(1+D^2) := by linarith
      convert mul_le_mul_of_nonneg_right he hA using 1; ring
    have he := ordinaryDerivativeWeight_error_rms (μ:=μ) (probabilityNodes (n+1)) (J 0) (J 1)
      (terminalActionChain_smooth hF x hr hl hT0 hT1 0).continuous
      (terminalActionChain_smooth hF x hr hl hT0 hT1 1).continuous
      ha0 hab (by positivity : 0≤2*(1+D^2)*A) hi hB
    dsimp only at he
    simp only [terminalQuadratureWeight,hc0,ite_false,probabilityNodeTime]
    refine ⟨he.1,he.2.trans ?_⟩
    have hr0 : 0≤probabilityCellLength T h c/logMeshNode T h c.val :=
      div_nonneg (probabilityCellLength_pos hT0 hT1 hh c).le ha0.le
    have hr4 := probabilityCellLength_ratio hT0 hT1 hh hL hs c hc0
    have hr16 : (probabilityCellLength T h c/logMeshNode T h c.val)^2≤16 := by
      nlinarith [sq_nonneg (4-probabilityCellLength T h c/logMeshNode T h c.val)]
    calc
      _ ≤ 16*(2*(1+D^2)*A) := mul_le_mul_of_nonneg_right hr16 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg H) hA]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma stronglyMeasurable_parametric_intervalIntegral (f : ℝ × Ω → E)
    (hf : StronglyMeasurable f) (a b : ℝ) :
    StronglyMeasurable (fun z => ∫t in a..b,f (t,z)) := by
  have he : StronglyMeasurable (fun z : Ω × ℝ => f (z.2,z.1)) :=
    hf.comp_measurable measurable_swap
  unfold intervalIntegral
  exact (he.integral_prod_right').sub (he.integral_prod_right')

lemma quadrature_error_sum {N : ℕ} {I : Type*} [Fintype I]
    (a : ℕ → ℝ) (f : ℝ → E) (v : Fin N → I → E) (w : Fin N → I → ℝ)
    (hi : ∀j,j<N → IntervalIntegrable f volume (a j) (a (j+1))) :
    (∫t in a 0..a N,f t)-(∑p : Fin N × I,w p.1 p.2 • v p.1 p.2)=
      ∑j : Fin N,((∫t in a j.val..a (j.val+1),f t)-∑i,w j i • v j i) := by
  rw [Finset.sum_sub_distrib,Fintype.sum_prod_type]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => ∫t in a j..a (j+1),f t)]
  exact (intervalIntegral.sum_integral_adjacent_intervals hi).symm
end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_analytic_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
    let err := fun z => (∫t in (0:ℝ)..T,t⁻¹ • J 1 (t,z))-
      ∑s,terminalQuadratureWeight T h n s • J 0 (probabilityNodeTime T h (n+1) s,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤(logMeshCount T h:ℝ)^2*(32*(1+D^2+H^2)*
        (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d) := by
  dsimp only
  let J := terminalActionChain hF x hr hl hT0 hT1
  let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
  let e := fun c : Fin (logMeshCount T h) => fun z =>
    (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
      ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)
  have hc := terminalActionChain_smooth hF x hr hl hT0 hT1
  have hm (c : Fin (logMeshCount T h)) : StronglyMeasurable (e c) := by
    apply StronglyMeasurable.sub
    · refine stronglyMeasurable_parametric_intervalIntegral (fun p => p.1⁻¹ • J 1 p) ?_ _ _
      exact (measurable_fst.inv.smul (hc 1).continuous.measurable).stronglyMeasurable
    · have hcj (i : Fin (n+2)) : Continuous (fun z : Point d × Point d =>
          terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)) := by
        have hscalar : Continuous (fun v : Point d => terminalQuadratureWeight T h n (c,i) • v) := continuous_const_smul _
        convert! hscalar.comp ((hc 0).continuous.comp
          ((continuous_const : Continuous (fun _ : Point d × Point d => probabilityNodeTime T h (n+1) (c,i))).prodMk continuous_id)) using 1
      exact (continuous_finsetSum _ (fun i _ => hcj i)).stronglyMeasurable
  have he := weighted_sum_sq (ν:=μ) (fun _ : Fin (logMeshCount T h) => (1:ℝ)) e
    (fun c => (hm c).aestronglyMeasurable)
    (fun c => (terminalQuadrature_cell_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL c).1)
    (fun c => (terminalQuadrature_cell_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL c).2)
  have heq (z : Point d × Point d) :
      (∫t in (0:ℝ)..T,t⁻¹ • J 1 (t,z))-
        ∑s,terminalQuadratureWeight T h n s • J 0 (probabilityNodeTime T h (n+1) s,z)=
      ∑c : Fin (logMeshCount T h),e c z := by
    have ht := quadrature_error_sum (logMeshNode T h) (fun t => t⁻¹ • J 1 (t,z))
      (fun c i => J 0 (probabilityNodeTime T h (n+1) (c,i),z))
      (fun c i => terminalQuadratureWeight T h n (c,i)) (fun j hj =>
        regularized_intervalIntegrable_nonneg
          ((hc 1).continuous.comp (continuous_id.prodMk continuous_const))
          (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 1 0 z).differentiableAt
          (terminalActionChain_first_zero hF x hr hlam hl hT0 hT1 z)
          (logMeshNode_mem hT0 hT1 hh hj.le).1
          (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self j)).le)
    simpa only [logMeshNode_zero,logMeshNode_last hT0 hT1 hh] using ht
  dsimp only [J] at heq
  simp_rw [heq]
  simpa only [one_smul,abs_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using he
end LogConcaveSampling

end

end

end OAI

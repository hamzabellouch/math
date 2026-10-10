import Mathlib
import OAI.Probability.LogConcave.Sampling.StateLaw
import OAI.Probability.LogConcave.Sampling.NoiseKernel

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R]

def changingChain (κ : ℕ → Kernel E E) (μ : Measure E) : ℕ → Measure E
  | 0 => μ
  | n+1 => κ n ∘ₘ changingChain κ μ n

instance changingChain_probability (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (changingChain κ μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => let := ih; exact inferInstanceAs (IsProbabilityMeasure (κ n ∘ₘ changingChain κ μ n))

lemma changingChain_constant (κ : Kernel E E) (μ : Measure E) (n : ℕ) :
    changingChain (fun _ => κ) μ n=markovChain κ μ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [changingChain,markovChain,ih]

lemma changingChain_tv (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {e : ℝ}
    (he : TVAtMost μ ν e) (n : ℕ) :
    TVAtMost (changingChain κ μ n) (changingChain κ ν n) e := by
  induction n with
  | zero => exact he
  | succ n ih => exact ih.kernel (κ n)

lemma stateLaw_eq_changingChain (μ : Measure E) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (f : ℕ → E × R → E) (hf : ∀n,Measurable (f n))
    (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    (hk : ∀n x,κ n x=γ.map (fun r => f n (x,r))) (n : ℕ) :
    stateLaw μ γ f n=changingChain κ μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateLaw,changingChain,ih]
    apply measure_eq_of_bounded_integral
    intro g hg hb
    rw [kernel_integral_comp _ _ hg hb,integral_map (hf n).aemeasurable hg.aestronglyMeasurable]
    rw [integral_prod _ (show Integrable (fun p => g (f n p)) _ from bounded_integrable (hg.comp (hf n)) (fun p => hb _))]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hk]
    exact (integral_map ((hf n).comp (show Measurable (fun r : R => (x,r)) by fun_prop)).aemeasurable hg.aestronglyMeasurable).symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma integral_norm_le_sqrt_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    (hm : MemLp (fun x : E => x) 2 μ) :
    (∫x,‖x‖ ∂μ)≤Real.sqrt (∫x,‖x‖^2 ∂μ) := by
  have hh := integral_mul_sq_le hm.norm (memLp_const (1:ℝ) (μ:=μ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).2 hh

lemma Admissible.first_moment_bound {V : Point d → ℝ} (hV : Admissible V) :
    Integrable (fun x => ‖x‖) (gibbs V) ∧ (∫x,‖x‖ ∂gibbs V)≤Real.sqrt d := by
  let := hV.isProbabilityMeasure_gibbs
  have hm : MemLp (fun x : Point d => x) 2 (gibbs V) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 hV.second_moment_bound.1
  exact ⟨hm.norm.integrable (by norm_num),(integral_norm_le_sqrt_moment hm).trans
    (Real.sqrt_le_sqrt hV.second_moment_bound.2)⟩

lemma stdGaussian_first_moment_bound (d : ℕ) :
    (∫x : Point d,‖x‖ ∂stdGaussian (Point d))≤Real.sqrt d := by
  simpa only [stdGaussian_sq_norm] using
    integral_norm_le_sqrt_moment (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))

lemma noisedLaw_first_moment {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    Integrable (fun x => ‖x‖) (noisedLaw V h) ∧
      (∫x,‖x‖ ∂noisedLaw V h)≤(1+Real.sqrt h)*Real.sqrt d := by
  let := hV.isProbabilityMeasure_gibbs
  have hiX : Integrable (fun p : Point d × Point d => ‖p.1‖)
      ((gibbs V).prod (stdGaussian (Point d))) := hV.first_moment_bound.1.comp_fst _
  have hiG : Integrable (fun p : Point d × Point d => ‖p.2‖)
      ((gibbs V).prod (stdGaussian (Point d))) :=
    (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable (by norm_num) |>.comp_snd _
  have hi : Integrable (fun p : Point d × Point d => ‖p.1+Real.sqrt h • p.2‖)
      ((gibbs V).prod (stdGaussian (Point d))) :=
    (hiX.add (hiG.const_mul (Real.sqrt h))).mono' (by fun_prop) (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      change ‖p.1+Real.sqrt h • p.2‖≤‖p.1‖+Real.sqrt h*‖p.2‖
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
        norm_add_le p.1 (Real.sqrt h • p.2)))
  refine ⟨(integrable_map_measure (by fun_prop) (by fun_prop)).2 hi,?_⟩
  rw [noisedLaw,integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫p : Point d × Point d,‖p.1‖+Real.sqrt h*‖p.2‖ ∂((gibbs V).prod (stdGaussian (Point d))) := by
      apply integral_mono hi (hiX.add (hiG.const_mul _))
      intro p
      change ‖p.1+Real.sqrt h • p.2‖≤‖p.1‖+Real.sqrt h*‖p.2‖
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
        norm_add_le p.1 (Real.sqrt h • p.2)
    _ = (∫x,‖x‖ ∂gibbs V)+Real.sqrt h*(∫x : Point d,‖x‖ ∂stdGaussian (Point d)) := by
      rw [integral_add hiX (hiG.const_mul _),integral_const_mul]
      simp only [integral_fun_fst,integral_fun_snd,probReal_univ,one_smul]
    _ ≤ Real.sqrt d+Real.sqrt h*Real.sqrt d := by
      exact add_le_add hV.first_moment_bound.2
        (mul_le_mul_of_nonneg_left (stdGaussian_first_moment_bound d) (Real.sqrt_nonneg _))
    _ = _ := by ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal RealInnerProductSpace

variable {d : ℕ}

lemma Admissible.value_difference_bound {V : Point d → ℝ} (hV : Admissible V)
    (x g : Point d) {s : ℝ} (hs : 0 ≤ s) :
    |V (x+s • g)-V x|≤ s*‖x‖^2+(s+s^2)*‖g‖^2 := by
  have ht := quadratic_remainder_of_gradient_lipschitz hV.smooth hV.gradient_lipschitz x (s • g)
  have hi := abs_real_inner_le_norm (s • g) (gradient V x)
  have hg := hV.gradient_norm_le x
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,NNReal.coe_ofNat] at ht hi
  have hh := abs_add_le (V (x+s • g)-V x-inner ℝ (s • g) (gradient V x))
    (inner ℝ (s • g) (gradient V x))
  have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg hs (norm_nonneg g))
  have hsq := mul_nonneg hs (sq_nonneg (‖x‖-‖g‖))
  ring_nf at hh
  nlinarith

theorem noisedLaw_tv {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    TVAtMost (noisedLaw V h) (gibbs V) (2*(2*Real.sqrt h+h)*d) := by
  let := hV.isProbabilityMeasure_gibbs
  have hVm := hV.smooth.continuous.measurable
  let := jointPosteriorLaw_probability hV h
  let H := fun p : Point d × Point d => -V p.1-‖p.2-p.1‖^2/(2*h)
  let c := (partition V)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt h)
  have hm : Measurable H := by have := hV.smooth.continuous.measurable; dsimp [H]; fun_prop
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.partition_ne_top)
    (EulerDensity.noiseCoefficient_positive d (Real.sqrt_pos.mpr hh).ne').ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.partition_pos.ne')
    (EulerDensity.noiseCoefficient_finite _ _)
  have hd : jointPosteriorLaw V h=MetropolisBalance.densityLaw volume c H := by
    have hd := EulerDensity.joint_density hV.smooth.continuous.measurable
      (fun z : Point d => z) measurable_id (Real.sqrt_pos.mpr hh).ne'
    simpa only [jointPosteriorLaw,MetropolisBalance.densityLaw,c,H,Real.sq_sqrt hh.le] using hd
  have he (p : Point d × Point d) : |H (p.1,p.1+Real.sqrt h • p.2)-H (p.1+Real.sqrt h • p.2,p.1)|
      =|V (p.1+Real.sqrt h • p.2)-V p.1| := by
    dsimp [H]
    rw [norm_sub_rev p.1 (p.1+Real.sqrt h • p.2)]
    congr 1
    ring
  let b := fun p : Point d × Point d => Real.sqrt h*‖p.1‖^2+(Real.sqrt h+h)*‖p.2‖^2
  have hib : Integrable b ((gibbs V).prod (stdGaussian (Point d))) :=
    (hV.second_moment_bound.1.comp_fst _ |>.const_mul _).add
      (((memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))).comp_snd _ |>.const_mul _)
  have hb (p : Point d × Point d) : |V (p.1+Real.sqrt h • p.2)-V p.1|≤b p := by
    simpa only [Real.sq_sqrt hh.le] using hV.value_difference_bound p.1 p.2 (Real.sqrt_nonneg h)
  have hir : Integrable (fun p : Point d × Point d => |H p-H p.swap|) (jointPosteriorLaw V h) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    apply hib.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by simpa only [comp_apply,Prod.swap_prod_mk,Real.norm_eq_abs,abs_abs,he] using hb p)
  have hr : (∫p,|H p-H p.swap| ∂jointPosteriorLaw V h)≤(2*Real.sqrt h+h)*d := by
    rw [jointPosteriorLaw,integral_map (by fun_prop) (by fun_prop)]
    simp only [Prod.swap_prod_mk]
    simp_rw [he]
    have hi : Integrable (fun p : Point d × Point d => |V (p.1+Real.sqrt h • p.2)-V p.1|)
        ((gibbs V).prod (stdGaussian (Point d))) :=
      hib.mono' (by fun_prop) (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_abs] using hb p))
    calc
      _ ≤ ∫p,b p ∂((gibbs V).prod (stdGaussian (Point d))) := integral_mono hi hib hb
      _ = Real.sqrt h*(∫x,‖x‖^2 ∂gibbs V)+(Real.sqrt h+h)*d := by
        dsimp only [b]
        rw [integral_add]
        · rw [integral_const_mul,integral_const_mul,integral_fun_fst (fun x : Point d => ‖x‖^2),integral_fun_snd (fun x : Point d => ‖x‖^2)]
          simp only [probReal_univ,one_smul,stdGaussian_sq_norm]
        · exact hV.second_moment_bound.1.comp_fst _ |>.const_mul _
        · simpa only [id_eq] using ((memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))).comp_snd ((gibbs V)) |>.const_mul (Real.sqrt h+h)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hV.second_moment_bound.2 (Real.sqrt_nonneg h)]
  let : IsFiniteMeasure (MetropolisBalance.densityLaw volume c H) := hd ▸ inferInstance
  intro A hA
  let f : Point d → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hbf (x) : |f x|≤1 := by by_cases hx : x∈A <;> simp [f,hx]
  have ht := MetropolisBalance.probability_one_step_defect volume hm hc0 hct
    (hd ▸ hir) hf (by norm_num : (0:ℝ)≤1) hbf
  rw [←hd] at ht
  have hs : (∫p : Point d × Point d,f p.2 ∂jointPosteriorLaw V h)=(noisedLaw V h).real A := by
    rw [←jointPosterior_snd (V:=V) h,←integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  have ht' : (∫p : Point d × Point d,f p.1 ∂jointPosteriorLaw V h)=(gibbs V).real A := by
    rw [←jointPosterior_fst (V:=V) h,←integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  rw [hs,ht'] at ht
  nlinarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

def descentScale (h : ℝ) (j : ℕ) : ℝ := h/2^j
lemma descentScale_pos {h : ℝ} (hh : 0<h) (j : ℕ) : 0<descentScale h j := by unfold descentScale; positivity
lemma descentScale_le {h : ℝ} (hh : 0≤h) (j : ℕ) : descentScale h j≤h := by
  exact div_le_self hh (one_le_pow₀ (by norm_num))
@[simp] lemma descentScale_zero (h : ℝ) : descentScale h 0=h := by simp [descentScale]
lemma descentScale_succ (h : ℝ) (j : ℕ) : descentScale h (j+1)=descentScale h j/2 := by simp [descentScale,pow_succ,div_div]

lemma halving_chain_error {V : Point d → ℝ} (hV : Admissible V) {h e : ℝ}
    (hh : 0<h) (hh1 : h≤1) (he : 0≤e)
    (κ : ℕ → Kernel (Point d) (Point d)) [∀j,IsMarkovKernel (κ j)]
    (hc : ∀j x,TVAtMost (κ j x) (halvingKernel V hV (descentScale h j) x)
      (2*e*(Real.sqrt d+2*Real.sqrt (descentScale h j)*‖x‖))) (j : ℕ) :
    TVAtMost (changingChain κ (noisedLaw V h) j) (noisedLaw V (descentScale h j))
      (j*(10*e*Real.sqrt d)) := by
  let := noisedLaw_probability hV h
  induction j with
  | zero => intro A hA; simp [changingChain]
  | succ j ih =>
    let hj := descentScale h j
    have hjp : 0<hj := descentScale_pos hh j
    have hj1 : hj≤1 := (descentScale_le hh.le j).trans hh1
    have hs : Real.sqrt hj≤1 := by simpa using Real.sqrt_le_sqrt hj1
    let := noisedLaw_probability hV hj
    let := halvingKernel_markov hV hjp
    let ei := fun x : Point d => 2*e*(Real.sqrt d+2*Real.sqrt hj*‖x‖)
    have hei : Integrable ei (noisedLaw V hj) := by
      exact ((integrable_const _).add ((noisedLaw_first_moment hV hj).1.const_mul _)).const_mul _
    have heint : (∫x,ei x ∂noisedLaw V hj)≤10*e*Real.sqrt d := by
      have hx := (noisedLaw_first_moment hV hj).2
      have hx' : (∫x,‖x‖ ∂noisedLaw V hj)≤2*Real.sqrt d := by
        nlinarith [Real.sqrt_nonneg (d:ℝ)]
      have hxs : Real.sqrt hj*(∫x,‖x‖ ∂noisedLaw V hj)≤2*Real.sqrt d := by
        exact (mul_le_mul_of_nonneg_right hs (integral_nonneg (fun _ => norm_nonneg _))).trans (by simpa using hx')
      dsimp only [ei]
      rw [integral_const_mul,integral_add (integrable_const _) ((noisedLaw_first_moment hV hj).1.const_mul _),integral_const_mul]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      nlinarith
    have hl := TVAtMost.kernel_mixture (noisedLaw V hj) (κ j) (halvingKernel V hV hj) hei (hc j)
    rw [halvingKernel_invariant hV hjp] at hl
    have ht := (ih.kernel (κ j)).trans hl
    change TVAtMost _ (noisedLaw V (hj/2)) _ at ht
    rw [changingChain,descentScale_succ]
    apply ht.mono
    push_cast
    nlinarith

namespace OracleCompiler
lemma approximateHalvingKernel_program (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (x : Point d) :
    approximateHalvingKernel S h V hV x=(gaussianTape d S.full.slots).map
      (fun g => (halvingProgram S h).run V (x,g)) := by
  have hm : Measurable (fun g => (proximalProgram S h).run V (x,g)) :=
    ((proximalProgram S h).measurable_run V hV.continuous_firstOrderReply.measurable).comp (by fun_prop)
  rw [approximateHalvingKernel_apply,approximateProximalKernel_apply,Measure.map_map (by fun_prop) hm]
  congr 1
  funext g
  rw [halvingProgram,Program.map_run]
  rfl
end OracleCompiler
end LogConcaveSampling

end

end

end OAI

import Mathlib
import OAI.Probability.ThreeState.PoissonBounds

namespace OAI

/-! Informative posterior mass and positive critical Poisson non-reconstruction. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

@[simp] lemma normalizer_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    normalizer lam h (fun _ : Fin n => uninformative) = 1 := by
  simp [normalizer,productWeight,edgeMessage,uninformative]

@[simp] lemma combineMessage_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    combineMessage lam h (fun _ : Fin n => uninformative) = uninformative := by
  simp only [combineMessage,normalizer_uninformative,one_ne_zero,↓reduceDIte,div_one]
  apply Subtype.ext
  funext i
  simp [productWeight,edgeMessage,uninformative]

lemma degreeOutput_atom (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (n : ℕ) :
    (Q : Measure Message) {uninformative}^n ≤ degreeOutput lam h Q n {uninformative} := by
  have hsub : {fun _ : Fin n => uninformative} ⊆ (combineMessage lam h) ⁻¹' {uninformative} := by
    intro m hm
    rcases Set.mem_singleton_iff.mp hm with rfl
    exact combineMessage_uninformative lam h n
  rw [degreeOutput, Measure.map_apply (measurable_combineMessage lam h n) (measurableSet_singleton _)]
  have hh := measure_mono (μ := degreeInput lam h Q n) hsub
  rw [degreeInput,withDensity_apply _ (measurableSet_singleton _),lintegral_singleton,
    normalizer_uninformative,ENNReal.ofReal_one,one_mul] at hh
  change (Measure.pi (fun _ : Fin n => (Q : Measure Message))) {fun _ => uninformative} ≤ _ at hh
  simpa [degreeInput] using hh

lemma densityEvolution_real (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (s : Set Message) (hs : MeasurableSet s) :
    (densityEvolution offspring lam h Q).real s = mean offspring (fun n => (degreeOutput lam h Q n).real s) := by
  rw [Measure.real,densityEvolution,Measure.sum_apply _ hs,ENNReal.tsum_toReal_eq]
  · simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,mean,mass,Measure.real]
  · intro n
    let := degreeOutput_probability lam h Q hQ n
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (offspring.apply_ne_top n) (measure_ne_top _ _)

lemma poisson_power_mean (d a : ℝ) (hd : 0 ≤ d) :
    mean (poissonOffspring d hd) (fun n => a^n) = Real.exp (d*(a-1)) := by
  have he (n : ℕ) : mass (poissonOffspring d hd) n*a^n = Real.exp (-d)*((d*a)^n/(n.factorial : ℝ)) := by
    rw [poisson_mass,mul_pow]
    ring
  unfold mean
  simp_rw [he]
  rw [tsum_mul_left]
  have hh := NormedSpace.expSeries_div_hasSum_exp (d*a)
  have he : (∑' n : ℕ, (d*a)^n/(n.factorial : ℝ)) = Real.exp (d*a) := by
    simpa only [← Real.exp_eq_exp_ℝ] using hh.tsum_eq
  rw [he,← Real.exp_add]
  congr 1
  ring

noncomputable def informativeMass (Q : ProbabilityMeasure Message) : ℝ :=
  1-(Q : Measure Message).real {uninformative}

lemma informativeMass_nonneg (Q : ProbabilityMeasure Message) : 0 ≤ informativeMass Q := by
  simp [informativeMass]

lemma informativeMass_le_one (Q : ProbabilityMeasure Message) : informativeMass Q ≤ 1 := by
  have hh := measureReal_nonneg (μ := (Q : Measure Message)) (s := {uninformative})
  dsimp only [informativeMass]
  linarith

lemma poisson_informative_recursion (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d hd) lam h Q) :
    Real.exp (-d*informativeMass Q) ≤ 1-informativeMass Q := by
  have hdegree (n : ℕ) : ((Q : Measure Message).real {uninformative})^n ≤ (degreeOutput lam h Q n).real {uninformative} := by
    let := degreeOutput_probability lam h Q hQ.1 n
    have ht := ENNReal.toReal_mono (measure_ne_top (degreeOutput lam h Q n) {uninformative}) (degreeOutput_atom lam h Q n)
    simpa only [ENNReal.toReal_pow,Measure.real] using ht
  have hf : HasMean (poissonOffspring d hd) (fun n => ((Q : Measure Message).real {uninformative})^n) := by
    apply hasMean_bounded _ 1
    intro n
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_one₀ (measureReal_nonneg) _
    simp
  have hg : HasMean (poissonOffspring d hd) (fun n => (degreeOutput lam h Q n).real {uninformative}) := by
    apply hasMean_bounded _ 1
    intro n
    let := degreeOutput_probability lam h Q hQ.1 n
    rw [abs_of_nonneg measureReal_nonneg]
    simp
  have hh := mean_nonneg (poissonOffspring d hd) (fun n => sub_nonneg.mpr (hdegree n))
  rw [mean_sub hg hf] at hh
  replace hh := sub_nonneg.mp hh
  rw [poisson_power_mean] at hh
  have he := congrArg (fun M : Measure Message => M.real {uninformative}) (fixedpoint_measure (poissonOffspring d hd) lam h Q hQ)
  rw [densityEvolution_real _ _ _ _ hQ.1 _ (measurableSet_singleton _)] at he
  rw [← he] at hh
  convert hh using 1 <;> dsimp only [informativeMass] <;> congr 1 <;> ring

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma integral_real_cauchy {α : Type*} [MeasurableSpace α] (M : Measure α) (f g : α → ℝ)
    (hf2 : Integrable (fun a => (f a)^2) M) (hg2 : Integrable (fun a => (g a)^2) M)
    (hfg : Integrable (fun a => f a*g a) M) :
    (∫ a, f a*g a ∂M)^2 ≤ (∫ a, (f a)^2 ∂M)*(∫ a, (g a)^2 ∂M) := by
  have hp (t : ℝ) : 0 ≤
      (∫ a, (f a)^2 ∂M)*(t*t)+(-2*(∫ a, f a*g a ∂M))*t+(∫ a, (g a)^2 ∂M) := by
    have hnon : 0 ≤ ∫ a, (t*f a-g a)^2 ∂M := integral_nonneg (fun value => sq_nonneg (t*f value-g value))
    have he (a : α) : (t*f a-g a)^2 = t^2*(f a)^2+(-2*t)*(f a*g a)+(g a)^2 := by ring
    simp_rw [he] at hnon
    have his : Integrable (fun a => t^2*(f a)^2+(-2*t)*(f a*g a)) M := (hf2.const_mul _).add (hfg.const_mul _)
    rw [integral_add his hg2, integral_add (hf2.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul] at hnon
    nlinarith only [hnon]
  have hh := discrim_le_zero hp
  simp only [discrim] at hh
  nlinarith only [hh]

@[simp] lemma messageX_uninformative : messageX uninformative = 0 := by
  simp [messageX,Radial.momentX,Radial.avg_expand,messageDeviation,uninformative]

lemma posteriorMu_sq_le_informative (Q : ProbabilityMeasure Message) :
    (posteriorMu Q)^2 ≤ informativeMass Q*posteriorNu Q := by
  let s : Set Message := {uninformative}ᶜ
  have hs : MeasurableSet s := (measurableSet_singleton _).compl
  let g : Message → ℝ := s.indicator (fun _ => 1)
  have hg : Integrable g (Q : Measure Message) := (integrable_const (1:ℝ)).indicator hs
  have hg2 : (fun m => (g m)^2) = g := by
    funext m
    by_cases hm : m∈s <;> simp [g,Set.indicator_of_mem,Set.indicator_of_notMem,hm]
  have hfg : (fun m => messageX m*g m) = messageX := by
    funext m
    by_cases hm : m∈s
    · simp [g,hm]
    · have he : m=uninformative := by simpa only [s,Set.mem_compl_iff,Set.mem_singleton_iff,not_not] using hm
      subst m
      simp
  have hh := integral_real_cauchy (Q : Measure Message) messageX g
    (integrable_continuous_message Q (continuous_messageX.pow 2))
    (by rw [hg2]; exact hg) (by rw [hfg]; exact integrable_continuous_message Q continuous_messageX)
  rw [hg2,hfg] at hh
  have hgint : (∫ m, g m ∂(Q : Measure Message))=informativeMass Q := by
    rw [show g=s.indicator (fun _ => (1:ℝ)) by rfl,integral_indicator hs]
    simp only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    change (Q : Measure Message).real {uninformative}ᶜ = 1-(Q : Measure Message).real {uninformative}
    rw [measureReal_compl (measurableSet_singleton _)]
    simp
  rw [hgint] at hh
  simpa only [posteriorMu,posteriorNu,mul_comm] using hh

lemma informativeMass_pos_of_mu_pos (Q : ProbabilityMeasure Message) (hm : 0 < posteriorMu Q) :
    0 < informativeMass Q := by
  have hh := posteriorMu_sq_le_informative Q
  apply lt_of_le_of_ne (informativeMass_nonneg Q)
  intro hzero
  rw [← hzero,zero_mul] at hh
  nlinarith only [hh,sq_pos_of_pos hm]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma poisson_positive_critical_uniform (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hc : d*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d (by linarith)) lam h Q)
    (hs : SpinSymmetric Q) : posteriorMu Q = 0 := by
  have hd0 : 0 < d := by linarith
  have hl1 : lam < 1 := by
    by_contra hn
    have hh : 1 ≤ lam^2 := by nlinarith [sq_nonneg (lam-1)]
    have hm := mul_le_mul_of_nonneg_left hh hd0.le
    nlinarith only [hm,hc,hd]
  have hD := (poisson_moments d hd0.le).hasMean
  have hc' : mean (poissonOffspring d hd0.le) (fun n : ℕ => (n:ℝ))*lam^2=1 := by
    simpa only [(poisson_moments d hd0.le).first] using hc
  have hh := positive_moment_estimates (poissonOffspring d hd0.le) lam h hl0 hl1 Q hQ hs hD hc'
  dsimp only at hh
  have hm := posteriorMu_nonneg Q
  have hn := posteriorNu_nonneg Q
  have he : 0 ≤ posteriorEta Q := (show 0 ≤ ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))*posteriorNu Q by positivity).trans hh.2.2.1
  have hent := poisson_entropy_bound d hd0 lam h hl0 hl1 hc Q hQ hs he
  have hcnu := critical_moment_nu_bound (poissonOffspring d hd0.le) lam h hl0 hl1 Q hQ hs hD hc'
  by_contra hzero
  have hmpos : 0 < posteriorMu Q := lt_of_le_of_ne hm (Ne.symm hzero)
  have hsp := informativeMass_pos_of_mu_pos Q hmpos
  apply PositiveScalar.moment_scalar_contradiction lam (posteriorMu Q) (posteriorNu Q)
    (∫ m, entropyJ m ∂(Q : Measure Message)) (informativeMass Q) hl0 hl1 hmpos hn hsp
    (informativeMass_le_one Q) (posteriorMu_sq_le_informative Q) hcnu hh.1 hh.2.1 hent
  intro _
  have hsb := poisson_support_bound d (informativeMass Q) hd0 hsp
    (poisson_informative_recursion d hd0.le lam h Q hQ)
  have heq : d⁻¹=lam^2 := by field_simp; nlinarith only [hc]
  rwa [heq] at hsb

 
theorem poisson_positive_critical_nonreconstruction (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (hl0 : 0 < lam) (hc : d*lam^2=1) :
    Tendsto (poissonAdvantage d (by linarith) lam h) atTop (𝓝 0) := by
  exact observed_tendsto_zero_of_uniform_fixedpoints (poissonOffspring d (by linarith)) lam h
    (poisson_positive_critical_uniform d hd lam h hl0 hc)

end ThreeState

end OAI

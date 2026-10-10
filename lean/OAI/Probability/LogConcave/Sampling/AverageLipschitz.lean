import Mathlib
import OAI.Probability.LogConcave.Sampling.ChangingChain

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma zero_average_lipschitz {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x => ‖x‖) μ) {f : Point d → ℝ}
    (hf : Measurable f) {C L : ℝ} (hb : ∀x,|f x|≤C)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    |f 0-(∫x,f x ∂μ)|≤L*(∫x,‖x‖ ∂μ) := by
  have he : f 0-(∫x,f x ∂μ)=∫x,(f 0-f x) ∂μ := by
    rw [integral_sub (integrable_const _) (bounded_integrable hf hb)]
    simp
  rw [he,←Real.norm_eq_abs,←integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ((integrable_const (f 0)).sub (bounded_integrable hf hb)).norm (hi.const_mul L)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs,dist_zero_left] using hl 0 x

lemma proximal_iterate_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C)
    (hb : ∀x,|f x|≤C) (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) (n : ℕ) :
    ∀x y,|markovAction (proximalKernel V hV h) n f x-markovAction (proximalKernel V hV h) n f y|
      ≤(L/(1+h)^n)*dist x y := by
  let := proximalKernel_markov hV hh
  induction n with
  | zero => simpa only [markovAction,iterate_zero,id_eq,pow_zero,div_one] using hl
  | succ n ih =>
    have he := proximal_action_lipschitz hV hh
      (markovAction_measurable _ hf n) hC (markovAction_bounded _ hC hb n) (by positivity) ih
    intro x y
    simp only [markovAction,iterate_succ_apply']
    convert! he x y using 1
    simp only [pow_succ,div_div]

lemma proximal_iterate_smoothing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} (hf : Measurable f) (hb : ∀x,0≤f x ∧ f x≤1) (n : ℕ) :
    ∀x y,|markovAction (proximalKernel V hV h) (n+1) f x-
      markovAction (proximalKernel V hV h) (n+1) f y|≤
      (1/((1+h)^(n+1)*Real.sqrt h))*dist x y := by
  let := proximalKernel_markov hV hh
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have he := proximal_iterate_lipschitz hV hh (kernelAction_measurable _ hf) (by norm_num : (0:ℝ)≤1)
    (kernelAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf)
    (by positivity : 0≤1/((1+h)*Real.sqrt h)) (proximal_action_smoothing hV hh hf hb) n
  intro x y
  simp only [markovAction,iterate_succ_apply]
  convert! he x y using 1
  congr 1
  simp only [div_div,pow_succ]
  congr 1
  ring

theorem proximal_chain_mixing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (n : ℕ) :
    TVAtMost (markovChain (proximalKernel V hV h) (Measure.dirac 0) (n+1)) (noisedLaw V h)
      (((1+Real.sqrt h)*Real.sqrt d)/((1+h)^(n+1)*Real.sqrt h)) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  intro A hA
  let f : Point d → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hb (x) : 0≤f x ∧ f x≤1 := by by_cases hx : x∈A <;> simp [f,hx]
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hact := markovChain_integral (proximalKernel V hV h) (Measure.dirac 0) hf (C:=1) (by norm_num) hbf (n+1)
  have hint := markovChain_integral (proximalKernel V hV h) (noisedLaw V h) hf (C:=1) (by norm_num) hbf (n+1)
  rw [markovChain_invariant _ _ (proximalKernel_invariant hV hh)] at hint
  have he := zero_average_lipschitz (noisedLaw_first_moment hV h).1
    (markovAction_measurable _ hf (n+1)) (markovAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf (n+1))
    (proximal_iterate_smoothing hV hh hf hb n)
  simp only [integral_dirac] at hact
  rw [←hint,←hact] at he
  have hif (μ : Measure (Point d)) : (∫x,f x ∂μ)=μ.real A := by
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  simp only [hif] at he
  apply he.trans
  calc
    _ ≤ (1/((1+h)^(n+1)*Real.sqrt h))*((1+Real.sqrt h)*Real.sqrt d) :=
      mul_le_mul_of_nonneg_left (noisedLaw_first_moment hV h).2 (by positivity)
    _ = _ := by ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma proximal_chain_observable {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C)
    (hb : ∀x,|f x|≤C) (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) (n : ℕ) :
    |(∫x,f x ∂markovChain (proximalKernel V hV h) (Measure.dirac 0) n)-
      (∫x,f x ∂noisedLaw V h)|≤L*((1+Real.sqrt h)*Real.sqrt d) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  have hact := markovChain_integral (proximalKernel V hV h) (Measure.dirac 0) hf hC hb n
  have hint := markovChain_integral (proximalKernel V hV h) (noisedLaw V h) hf hC hb n
  rw [markovChain_invariant _ _ (proximalKernel_invariant hV hh)] at hint
  have he := zero_average_lipschitz (noisedLaw_first_moment hV h).1
    (markovAction_measurable _ hf n) (markovAction_bounded _ hC hb n)
    (proximal_iterate_lipschitz hV hh hf hC hb hL hl n)
  simp only [integral_dirac] at hact
  rw [←hint,←hact] at he
  apply he.trans
  have hpow : (1:ℝ)≤(1+h)^n := one_le_pow₀ (by linarith)
  have hdv : L/(1+h)^n≤L := (div_le_self hL hpow)
  exact mul_le_mul hdv (noisedLaw_first_moment hV h).2 (integral_nonneg (fun _ => norm_nonneg _)) hL

lemma TVAtMost.cap_one {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {e : ℝ} (he : TVAtMost μ ν e) : TVAtMost μ ν (min e 1) := by
  intro A hA
  refine le_min (he A hA) ?_
  exact abs_sub_le_iff.mpr ⟨by linarith [measureReal_le_one (μ:=μ) (s:=A),measureReal_nonneg (μ:=ν) (s:=A)],
    by linarith [measureReal_le_one (μ:=ν) (s:=A),measureReal_nonneg (μ:=μ) (s:=A)]⟩

lemma proximal_local_cap_lipschitz {a b : ℝ} (hb : 0≤b) :
    ∀x y : Point d,|min (a+b*‖x‖) 1-min (a+b*‖y‖) 1|≤b*dist x y := by
  intro x y
  have ht := abs_min_sub_min_le_max (a+b*‖x‖) (1:ℝ) (a+b*‖y‖) 1
  simp only [sub_self,abs_zero] at ht
  apply ht.trans
  have he : a+b*‖x‖-(a+b*‖y‖)=b*(‖x‖-‖y‖) := by ring
  rw [he,abs_mul,abs_of_nonneg hb]
  apply max_le
  · simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) hb
  · positivity

theorem proximal_chain_perturbation {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (κ : Kernel (Point d) (Point d)) [IsMarkovKernel κ] {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (he : ∀x,TVAtMost (κ x) (proximalKernel V hV h x) (a+b*‖x‖)) (n : ℕ) :
    TVAtMost (markovChain κ (Measure.dirac 0) n)
      (markovChain (proximalKernel V hV h) (Measure.dirac 0) n)
      (n*(a+2*b*((1+Real.sqrt h)*Real.sqrt d))) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  let e : Point d → ℝ := fun x => min (a+b*‖x‖) 1
  have hm : Measurable e := by dsimp [e]; fun_prop
  have he0 (x) : 0≤e x := le_min (by positivity) (by norm_num)
  have he1 (x) : |e x|≤1 := by rw [abs_of_nonneg (he0 x)]; exact min_le_right _ _
  apply markovChain_perturbation κ (proximalKernel V hV h) (Measure.dirac 0)
    (fun x => (he x).cap_one) (fun n => bounded_integrable hm he1)
  intro k
  have hstat : (∫x,e x ∂noisedLaw V h)≤a+b*((1+Real.sqrt h)*Real.sqrt d) := by
    calc
      _ ≤ ∫x,(a+b*‖x‖) ∂noisedLaw V h := integral_mono (bounded_integrable hm he1)
        ((integrable_const a).add ((noisedLaw_first_moment hV h).1.const_mul b))
        (fun x => min_le_left _ _)
      _ = a+b*(∫x,‖x‖ ∂noisedLaw V h) := by
        rw [integral_add (integrable_const a) ((noisedLaw_first_moment hV h).1.const_mul b),integral_const_mul]
        simp
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (noisedLaw_first_moment hV h).2 hb) a
  have hc := proximal_chain_observable hV hh hm (by norm_num : (0:ℝ)≤1) he1 hb
    (proximal_local_cap_lipschitz hb) k
  linarith [(le_abs_self ((∫x,e x ∂markovChain (proximalKernel V hV h) (Measure.dirac 0) k)-
      (∫x,e x ∂noisedLaw V h)))]

end LogConcaveSampling

end

end

end OAI

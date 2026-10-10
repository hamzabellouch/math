import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TvPre
import OAI.Probability.LogConcave.Sampling.PosteriorJointIntegral
import OAI.Probability.LogConcave.Dynamics.IntegralLipschitz

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

def noiseKernel (s : ℝ) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ Kernel.const (Point d) (stdGaussian (Point d))).map (fun p => p.1+s • p.2)

instance noiseKernel_markov (s : ℝ) : IsMarkovKernel (noiseKernel (d:=d) s) := by
  unfold noiseKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma noiseKernel_apply (s : ℝ) (x : Point d) :
    noiseKernel s x=(stdGaussian (Point d)).map (fun z => x+s • z) := by
  rw [noiseKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma noiseKernel_comp (s : ℝ) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    noiseKernel s ∘ₘ μ=(μ.prod (stdGaussian (Point d))).map (fun p => p.1+s • p.2) := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.map_apply (by fun_prop) hA,
    Measure.prod_apply (hA.preimage (by fun_prop))]
  apply lintegral_congr
  intro x
  rw [noiseKernel_apply,Measure.map_apply (by fun_prop) hA]
  rfl

def proximalKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  noiseKernel (Real.sqrt h) ∘ₖ posteriorKernel V hV h

lemma proximalKernel_markov {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    IsMarkovKernel (proximalKernel V hV h) := by
  let := posteriorKernel_probability hV hh
  unfold proximalKernel
  infer_instance

lemma measure_eq_of_bounded_integral {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀f : E → ℝ,Measurable f → (∀x,|f x|≤1) → (∫x,f x ∂μ)=∫x,f x ∂ν) : μ=ν := by
  ext s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have he := h (s.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hs)
    (fun x => by by_cases hx : x∈s <;> simp [hx])
  simpa only [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one,measureReal_def] using he

lemma posteriorKernel_invariant {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) : posteriorKernel V hV h ∘ₘ noisedLaw V h=gibbs V := by
  let := hV.isProbabilityMeasure_gibbs
  let := posteriorKernel_probability hV hh
  let := noisedLaw_probability hV h
  apply measure_eq_of_bounded_integral
  intro f hf hb
  rw [kernel_integral_comp _ _ hf hb]
  exact posterior_reconstruction_integral hV hh hf (by norm_num) hb

lemma proximalKernel_invariant {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) : proximalKernel V hV h ∘ₘ noisedLaw V h=noisedLaw V h := by
  let := hV.isProbabilityMeasure_gibbs
  rw [proximalKernel,←Measure.comp_assoc,posteriorKernel_invariant hV hh,
    noiseKernel_comp]
  rfl

def kernelAction {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) (f : F → ℝ) : E → ℝ := fun x => ∫z,f z ∂κ x

lemma kernelAction_measurable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsSFiniteKernel κ] {f : F → ℝ} (hf : Measurable f) :
    Measurable (kernelAction κ f) := hf.stronglyMeasurable.integral_kernel.measurable

lemma kernelAction_bounded {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ] {f : F → ℝ} {C : ℝ} (hC : 0≤C)
    (hb : ∀x,|f x|≤C) : ∀x,|kernelAction κ f x|≤C := fun _ => bounded_integral hC hb

lemma kernelAction_unit {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ] {f : F → ℝ} (_hf : Measurable f)
    (hb : ∀x,0≤f x ∧ f x≤1) : ∀x,0≤kernelAction κ f x ∧ kernelAction κ f x≤1 := by
  intro x
  refine ⟨integral_nonneg (fun z => (hb z).1),?_⟩
  exact (le_abs_self _).trans (kernelAction_bounded κ (by norm_num : (0:ℝ)≤1)
    (fun z => by rw [abs_of_nonneg (hb z).1]; exact (hb z).2) x)

lemma kernelAction_comp {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (κ : Kernel E F) (η : Kernel F G)
    [IsMarkovKernel κ] [IsMarkovKernel η] {f : G → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀x,|f x|≤C) : kernelAction (η ∘ₖ κ) f=kernelAction κ (kernelAction η f) := by
  funext x
  exact Kernel.integral_comp (bounded_integrable hf hb)

lemma noiseKernel_action_lipschitz (s : ℝ) {f : Point d → ℝ} {L C : ℝ}
    (hf : Measurable f) (hb : ∀x,|f x|≤C) (_hL : 0≤L)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    ∀x y,|kernelAction (noiseKernel s) f x-kernelAction (noiseKernel s) f y|≤L*dist x y := by
  intro x y
  have hx : Measurable (fun z : Point d => f (x+s • z)) := hf.comp (by fun_prop)
  have hy : Measurable (fun z : Point d => f (y+s • z)) := hf.comp (by fun_prop)
  simp only [kernelAction,noiseKernel_apply]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_map (by fun_prop) hf.aestronglyMeasurable,
    ←integral_sub (bounded_integrable hx (fun z => hb _)) (bounded_integrable hy (fun z => hb _)),
    ←Real.norm_eq_abs]
  have ht := norm_integral_le_of_norm_le_const (f:=fun z : Point d => f (x+s • z)-f (y+s • z))
    (μ:=stdGaussian (Point d)) (C:=L*dist x y) (Filter.Eventually.of_forall (fun z : Point d => by
    simpa only [Real.norm_eq_abs,dist_add_right] using hl (x+s • z) (y+s • z)))
  simpa [measureReal_def] using ht

lemma proximal_action_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C) (hb : ∀x,|f x|≤C)
    (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) :
    ∀x y,|kernelAction (proximalKernel V hV h) f x-kernelAction (proximalKernel V hV h) f y|
      ≤(L/(1+h))*dist x y := by
  let := posteriorKernel_probability hV hh
  rw [proximalKernel,kernelAction_comp _ _ hf hb]
  intro x y
  have he := (posterior_distanceCoupled hV hh x y).integral_lipschitz hL
    (kernelAction_measurable (noiseKernel (Real.sqrt h)) hf) (kernelAction_bounded _ hC hb)
    (noiseKernel_action_lipschitz (Real.sqrt h) hf hb hL hl)
  convert! he using 1
  simp only [div_eq_mul_inv]
  ring

lemma proximal_action_smoothing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} (hf : Measurable f) (hb : ∀x,0≤f x ∧ f x≤1) :
    ∀x y,|kernelAction (proximalKernel V hV h) f x-kernelAction (proximalKernel V hV h) f y|
      ≤(1/((1+h)*Real.sqrt h))*dist x y := by
  let := posteriorKernel_probability hV hh
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  rw [proximalKernel,kernelAction_comp _ _ hf hbf]
  have hn : ∀x y,|kernelAction (noiseKernel (Real.sqrt h)) f x-
      kernelAction (noiseKernel (Real.sqrt h)) f y|≤(1/Real.sqrt h)*dist x y := by
    intro x y
    have htv : TVAtMost (noiseKernel (Real.sqrt h) x) (noiseKernel (Real.sqrt h) y) (‖x-y‖/Real.sqrt h) := by
      simpa only [noiseKernel_apply] using TVAtMost_gaussian_affine x y (Real.sqrt_pos.mpr hh)
    have ht := htv.integral_unit hf hb
    simpa only [kernelAction,noiseKernel_apply,dist_eq_norm,one_div,div_eq_inv_mul,mul_one] using ht
  intro x y
  have he := (posterior_distanceCoupled hV hh x y).integral_lipschitz
    (by positivity : 0≤1/Real.sqrt h) (kernelAction_measurable _ hf)
    (kernelAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf) hn
  convert! he using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

lemma affine_primitive_posterior {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (y : Point d) :
    (gibbs (primitivePotential (affinePotential V y (Real.sqrt h)) 0 1)).map
      (fun z => y+Real.sqrt h • z)=gibbs (posteriorPotential V h y) := by
  have hs := (Real.sqrt_pos.mpr hh).ne'
  rw [gibbs_map_affine ((hV.affinePrimitive y (Real.sqrt h)).continuous_potential 0 1) y hs]
  congr 1
  funext z
  have ha : y+Real.sqrt h • ((Real.sqrt h)⁻¹ • (z-y))=z := by
    rw [smul_smul,mul_inv_cancel₀ hs,one_smul]; abel
  simp only [primitivePotential,affinePotential,one_smul,zero_add,ha,posteriorPotential,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,Real.sq_sqrt hh.le]
  ring

lemma noised_affine_law (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (y : Point d) (s : ℝ) :
    (((μ.prod (stdGaussian (Point d))).map (fun z => z.1+z.2)).map (fun z => y+s • z))=
      noiseKernel s ∘ₘ μ.map (fun z => y+s • z) := by
  rw [noiseKernel_comp,Measure.map_map (by fun_prop) (by fun_prop)]
  have hp := Measure.map_prod_map μ (stdGaussian (Point d))
    (show Measurable (fun z => y+s • z) by fun_prop) measurable_id
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  change y+s • (p.1+p.2)=(y+s • p.1)+s • p.2
  rw [smul_add,add_assoc]

namespace OracleCompiler

def proximalProgram (S : ReservedProgram d) (h : ℝ) :
    Program (Point d × (Fin S.full.slots → Point d)) d S.full.calls (Point d) :=
  (((S.full.program.seedMap (fun p : Point d × (Fin S.full.slots → Point d) => (0,p.2))
      (by fun_prop)).affineOracle Prod.fst measurable_fst (Real.sqrt h))).map
    (fun p => p.1.1+Real.sqrt h • p.2) (by fun_prop)

lemma proximalProgram_run (S : ReservedProgram d) (h : ℝ) {V : Point d → ℝ} (hV : Admissible V)
    (y : Point d) (g : Fin S.full.slots → Point d) :
    (proximalProgram S h).run V (y,g)=
      y+Real.sqrt h • S.full.program.run (affinePotential V y (Real.sqrt h)) (0,g) := by
  rw [proximalProgram,Program.map_run,Program.affineOracle_run _ _ _ _ hV.smooth,Program.seedMap_run]

def approximateProximalKernel (S : ReservedProgram d) (h : ℝ)
    (V : Point d → ℝ) (_hV : Admissible V) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ Kernel.const (Point d) (gaussianTape d S.full.slots)).map
    ((proximalProgram S h).run V)

lemma approximateProximalKernel_markov (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) : IsMarkovKernel (approximateProximalKernel S h V hV) := by
  unfold approximateProximalKernel
  apply Kernel.IsMarkovKernel.map
  exact (proximalProgram S h).measurable_run V
    (hV.smooth.continuous.measurable.prodMk hV.gradient_lipschitz.continuous.measurable)

lemma approximateProximalKernel_apply (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (y : Point d) :
    approximateProximalKernel S h V hV y=
      (gaussianTape d S.full.slots).map (fun g => (proximalProgram S h).run V (y,g)) := by
  have hm := (proximalProgram S h).measurable_run V
    (hV.smooth.continuous.measurable.prodMk hV.gradient_lipschitz.continuous.measurable)
  rw [approximateProximalKernel,Kernel.map_apply _ hm,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map hm (by fun_prop)]
  rfl

lemma approximateProximalKernel_tv (S : ℝ → ℝ → ReservedProgram d)
    {V : Point d → ℝ} (hV : Admissible V) {h q K e ηmin : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀y,SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S)
    (y : Point d) :
    TVAtMost (approximateProximalKernel (S 1 1) h V hV y) (proximalKernel V hV h y)
      (2*e*(Real.sqrt d+2*Real.sqrt h*‖y‖)) := by
  let F := affinePotential V y (Real.sqrt h)
  have hF := hV.affinePrimitive y (Real.sqrt h)
  have hs : SampleSize (2*h) q 1 1 := by
    unfold SampleSize
    norm_num
    exact hq
  have hl : (2*(Real.sqrt h)^2)*1^2<1 := by rw [Real.sq_sqrt hh.le]; nlinarith
  have hpre := (hc y).error 1 1 hs hη 0
  have ht := (S 1 1).tv_of_pre hF 0 (r:=1) (η:=1) (by norm_num) hl
    (by norm_num) he hres hpre
  have hf : Measurable (fun g => (S 1 1).full.program.run F (0,g)) :=
    ((S 1 1).full.program.measurable_run F
      (hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable)).comp (by fun_prop)
  have hh' := ht.map (show Measurable (fun z : Point d => y+Real.sqrt h • z) by fun_prop)
  have hprob : IsProbabilityMeasure (gibbs (primitivePotential F 0 1)) :=
    probability_gibbs_of_partition (partition_pos_of_continuous (hF.continuous_potential 0 1)).ne'
      (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential 0 (by norm_num) hl))
  let := hprob
  simp only [one_smul,div_one] at hh'
  rw [noised_affine_law,affine_primitive_posterior hV hh y] at hh'
  rw [Measure.map_map (by fun_prop) hf] at hh'
  have hleft : ((gaussianTape d (S 1 1).full.slots).map
      ((fun z : Point d => y+Real.sqrt h • z) ∘ (fun g => (S 1 1).full.program.run F (0,g))))=
      approximateProximalKernel (S 1 1) h V hV y := by
    rw [approximateProximalKernel_apply]
    congr 1
    funext g
    exact (proximalProgram_run _ _ hV y g).symm
  rw [hleft] at hh'
  change TVAtMost _ (proximalKernel V hV h y) _ at hh'
  apply hh'.mono
  have hg : ‖gradient F 0‖≤2*Real.sqrt h*‖y‖ := by
    rw [gradient_affinePotential hV.smooth]
    simp only [smul_zero,add_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left (hV.gradient_norm_le y) (Real.sqrt_nonneg h)]
  unfold circuitD
  exact mul_le_mul_of_nonneg_left (by simpa only [F] using add_le_add_right hg (Real.sqrt d)) (by positivity)

end OracleCompiler
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

lemma posterior_joint_reconstruction {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {f : Point d × Point d → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀p,|f p|≤C) :
    (∫y,(∫z,f (z,y) ∂gibbs (posteriorPotential V h y)) ∂noisedLaw V h)=
      ∫p,f p ∂jointPosteriorLaw V h := by
  let := hV.isProbabilityMeasure_gibbs
  let := noisedLaw_probability hV h
  let := jointPosteriorLaw_probability hV h
  let := posteriorKernel_probability hV hh
  let g := fun y => ∫z,f (z,y) ∂gibbs (posteriorPotential V h y)
  have hg : Measurable g := (hf.stronglyMeasurable.integral_kernel_prod_left'
    (κ:=posteriorKernel V hV h)).measurable
  have hgb (y : Point d) : |g y|≤C := by
    let : IsProbabilityMeasure (gibbs (posteriorPotential V h y)) :=
      (posteriorKernel_probability hV hh).isProbabilityMeasure y
    exact bounded_integral hC (fun z => hb (z,y))
  have hif := bounded_integrable hf hb (μ:=jointPosteriorLaw V h)
  have hiy := bounded_integrable (hg.comp measurable_snd) (fun p : Point d × Point d => hgb p.2)
    (μ:=jointPosteriorLaw V h)
  have hz := posterior_joint_integral_zero hV hh (hif.sub hiy) (fun y => by
    simp only [Pi.sub_apply,comp_apply]
    let : IsProbabilityMeasure (gibbs (posteriorPotential V h y)) := (posteriorKernel_probability hV hh).isProbabilityMeasure y
    rw [integral_sub]
    · simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,g,sub_self]
    · exact bounded_integrable (hf.comp (show Measurable (fun z : Point d => (z,y)) by fun_prop)) (fun z => hb (z,y))
    · exact integrable_const (g y))
  simp only [Pi.sub_apply] at hz
  rw [integral_sub hif hiy] at hz
  have hgy : (∫p : Point d × Point d,g p.2 ∂jointPosteriorLaw V h)=∫y,g y ∂noisedLaw V h := by
    rw [←jointPosterior_snd (V:=V) h,integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]
  simp only [comp_apply] at hz
  rw [hgy] at hz
  exact (sub_eq_zero.mp hz).symm

def halvingKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ proximalKernel V hV h).map (fun p => (1/2:ℝ) • (p.1+p.2))

lemma halvingKernel_markov {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    IsMarkovKernel (halvingKernel V hV h) := by
  let := proximalKernel_markov hV hh
  unfold halvingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma halvingKernel_apply {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) (y : Point d) :
    halvingKernel V hV h y=(proximalKernel V hV h y).map (fun z => (1/2:ℝ) • (y+z)) := by
  let := proximalKernel_markov hV hh
  rw [halvingKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma halving_gaussian_law {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    ((jointPosteriorLaw V h).prod (stdGaussian (Point d))).map
      (fun p => (1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))=noisedLaw V (h/2) := by
  let := hV.isProbabilityMeasure_gibbs
  let := jointPosteriorLaw_probability hV h
  have hv : (Real.sqrt h/2)^2+(Real.sqrt h/2)^2=(Real.sqrt (h/2))^2 := by
    rw [Real.sq_sqrt (by positivity : 0≤h/2)]
    nlinarith [Real.sq_sqrt hh.le]
  have hm : (jointPosteriorLaw V h).map (fun p => (1/2:ℝ) • (p.1+p.2))=
      ((gibbs V).prod (stdGaussian (Point d))).map (fun p => p.1+(Real.sqrt h/2) • p.2) := by
    rw [jointPosteriorLaw,Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    change (1/2:ℝ) • (p.1+(p.1+Real.sqrt h • p.2))=_
    module
  have hl := smoothing_add_gaussian (jointPosteriorLaw V h) (gibbs V)
    (fun p => (1/2:ℝ) • (p.1+p.2)) id (by fun_prop) measurable_id
    (Real.sqrt h/2) (Real.sqrt h/2) (Real.sqrt (h/2)) hv hm
  convert! hl using 1
  congr 1
  funext p
  module

lemma halvingKernel_invariant {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    halvingKernel V hV h ∘ₘ noisedLaw V h=noisedLaw V (h/2) := by
  let := halvingKernel_markov hV hh
  let := proximalKernel_markov hV hh
  let := posteriorKernel_probability hV hh
  let := noisedLaw_probability hV h
  let := noisedLaw_probability hV (h/2)
  let := jointPosteriorLaw_probability hV h
  apply measure_eq_of_bounded_integral
  intro f hf hb
  rw [kernel_integral_comp _ _ hf hb]
  let u : Point d × Point d → ℝ := fun p => ∫g,f ((1/2:ℝ) • (p.1+p.2+Real.sqrt h • g)) ∂stdGaussian (Point d)
  have hu : Measurable u := (show Measurable (fun p : (Point d × Point d) × Point d =>
    f ((1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))) from hf.comp (by fun_prop)).stronglyMeasurable.integral_prod_right.measurable
  have hub (p) : |u p|≤1 := bounded_integral (by norm_num) (fun g => hb _)
  have he := posterior_joint_reconstruction hV hh hu (by norm_num : (0:ℝ)≤1) hub
  have hfib (y : Point d) : (∫z,f z ∂halvingKernel V hV h y)=
      ∫z,u (z,y) ∂gibbs (posteriorPotential V h y) := by
    rw [halvingKernel_apply hV hh,integral_map (by fun_prop) hf.aestronglyMeasurable]
    change kernelAction (proximalKernel V hV h) (fun z => f ((1/2:ℝ) • (y+z))) y=_
    rw [proximalKernel]
    rw [kernelAction_comp _ _ (show Measurable (fun z : Point d => f ((1/2:ℝ) • (y+z))) from hf.comp (by fun_prop)) (fun z => hb _)]
    unfold kernelAction
    apply integral_congr_ae
    filter_upwards [] with z
    rw [noiseKernel_apply,integral_map (by fun_prop) (show Measurable (fun z : Point d => f ((1/2:ℝ) • (y+z))) from hf.comp (by fun_prop)).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with g
    congr 1
    module
  simp_rw [hfib]
  rw [he,←halving_gaussian_law hV hh,integral_map (by fun_prop) hf.aestronglyMeasurable]
  exact (integral_prod _ (bounded_integrable (show Measurable (fun p : (Point d × Point d) × Point d => f ((1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))) from hf.comp (by fun_prop)) (fun p => hb _))).symm

namespace OracleCompiler

def halvingProgram (S : ReservedProgram d) (h : ℝ) :
    Program (Point d × (Fin S.full.slots → Point d)) d S.full.calls (Point d) :=
  (proximalProgram S h).map (fun p => (1/2:ℝ) • (p.1.1+p.2)) (by fun_prop)

def approximateHalvingKernel (S : ReservedProgram d) (h : ℝ)
    (V : Point d → ℝ) (hV : Admissible V) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ approximateProximalKernel S h V hV).map (fun p => (1/2:ℝ) • (p.1+p.2))

lemma approximateHalvingKernel_markov (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) : IsMarkovKernel (approximateHalvingKernel S h V hV) := by
  let := approximateProximalKernel_markov S h hV
  unfold approximateHalvingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma approximateHalvingKernel_apply (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (y : Point d) :
    approximateHalvingKernel S h V hV y=
      (approximateProximalKernel S h V hV y).map (fun z => (1/2:ℝ) • (y+z)) := by
  let := approximateProximalKernel_markov S h hV
  rw [approximateHalvingKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma approximateHalvingKernel_tv (S : ℝ → ℝ → ReservedProgram d)
    {V : Point d → ℝ} (hV : Admissible V) {h q K e ηmin : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀y,SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S)
    (y : Point d) :
    TVAtMost (approximateHalvingKernel (S 1 1) h V hV y) (halvingKernel V hV h y)
      (2*e*(Real.sqrt d+2*Real.sqrt h*‖y‖)) := by
  rw [approximateHalvingKernel_apply,halvingKernel_apply hV hh]
  exact (approximateProximalKernel_tv S hV hh hq hq1 he hη hres hc y).map (by fun_prop)

end OracleCompiler
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E : Type*} [MeasurableSpace E]

def markovChain (κ : Kernel E E) (μ : Measure E) : ℕ → Measure E
  | 0 => μ
  | n+1 => κ ∘ₘ markovChain κ μ n

instance markovChain_probability (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (markovChain κ μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => let := ih; exact inferInstanceAs (IsProbabilityMeasure (κ ∘ₘ markovChain κ μ n))

def markovAction (κ : Kernel E E) (n : ℕ) (f : E → ℝ) : E → ℝ :=
  (kernelAction κ)^[n] f

lemma markovAction_measurable (κ : Kernel E E) [IsMarkovKernel κ]
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) : Measurable (markovAction κ n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    simpa only [markovAction,iterate_succ_apply'] using kernelAction_measurable κ ih

lemma markovAction_bounded (κ : Kernel E E) [IsMarkovKernel κ]
    {f : E → ℝ} {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) (n : ℕ) :
    ∀x,|markovAction κ n f x|≤C := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    simpa only [markovAction,iterate_succ_apply'] using kernelAction_bounded κ hC ih

lemma markovAction_unit (κ : Kernel E E) [IsMarkovKernel κ]
    {f : E → ℝ} (hf : Measurable f) (hb : ∀x,0≤f x ∧ f x≤1) (n : ℕ) :
    ∀x,0 ≤ markovAction κ n f x ∧ markovAction κ n f x≤1 := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    simpa only [markovAction,iterate_succ_apply'] using kernelAction_unit κ (markovAction_measurable κ hf n) ih

lemma markovChain_integral (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) (n : ℕ) :
    (∫x,f x ∂markovChain κ μ n)=∫x,markovAction κ n f x ∂μ := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [markovChain,kernel_integral_comp _ _ hf hb]
    change (∫x,kernelAction κ f x ∂markovChain κ μ n)=_
    rw [ih (kernelAction_measurable κ hf) (kernelAction_bounded κ hC hb)]
    rfl

lemma markovChain_invariant (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) (hμ : κ ∘ₘ μ=μ) (n : ℕ) : markovChain κ μ n=μ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [markovChain,ih,hμ]

lemma markovChain_perturbation (κ η : Kernel E E) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure E) [IsProbabilityMeasure μ] {e : E → ℝ} {a : ℝ}
    (he : ∀x,TVAtMost (κ x) (η x) (e x))
    (hi : ∀n,Integrable e (markovChain η μ n))
    (ha : ∀n,(∫x,e x ∂markovChain η μ n)≤a) (n : ℕ) :
    TVAtMost (markovChain κ μ n) (markovChain η μ n) (n*a) := by
  induction n with
  | zero => intro s hs; simp [markovChain]
  | succ n ih =>
    have hh := (ih.kernel κ).trans (TVAtMost.kernel_mixture (markovChain η μ n) κ η (hi n) he)
    apply hh.mono
    push_cast
    linarith [ha n]

end LogConcaveSampling

end

end

end OAI

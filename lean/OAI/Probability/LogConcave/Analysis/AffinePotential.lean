import Mathlib
import OAI.Probability.LogConcave.JetEstimates.CrossMoment
import OAI.Probability.LogConcave.OraclePrograms.Program
import OAI.Probability.LogConcave.Sampling.Map

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped Classical NNReal RealInnerProductSpace

variable {d : ℕ}

def affinePotential (V : Point d → ℝ) (a : Point d) (s : ℝ) : Point d → ℝ :=
  fun z => V (a+s • z)

lemma gradient_affinePotential {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
    (a : Point d) (s : ℝ) (z : Point d) :
    gradient (affinePotential V a s) z=s • gradient V (a+s • z) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha : HasFDerivAt (fun w : Point d => a+s • w)
      (0+s • ContinuousLinearMap.id ℝ (Point d)) z :=
    (hasFDerivAt_const a z).add ((hasFDerivAt_id z).const_smul s)
  have hb := (hV.differentiable (by norm_num) (a+s • z)).hasFDerivAt.comp z ha
  convert! hb using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,zero_add,ContinuousLinearMap.map_smul,smul_eq_mul]
  change inner ℝ (s • gradient V (a+s • z)) v=s*(fderiv ℝ V (a+s • z)) v
  rw [real_inner_smul_left,←toDual_gradient]
  rfl

lemma Admissible.affinePrimitive {V : Point d → ℝ} (hV : Admissible V)
    (a : Point d) (s : ℝ) : Primitive (affinePotential V a s) ⟨2*s^2,by positivity⟩ := by
  constructor
  · exact hV.smooth.comp (contDiff_const.add (contDiff_id.const_smul s))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [gradient_affinePotential hV.smooth,gradient_affinePotential hV.smooth,dist_smul₀]
    have hh := hV.gradient_lipschitz.dist_le_mul (a+s • x) (a+s • y)
    rw [dist_add_left,dist_smul₀] at hh
    have hb := mul_le_mul_of_nonneg_left hh (norm_nonneg s)
    change ‖s‖ * dist (gradient V (a+s • x)) (gradient V (a+s • y)) ≤ (2*s^2)*dist x y
    calc
      _ ≤ ‖s‖*(2*(‖s‖*dist x y)) := hb
      _ = _ := by rw [Real.norm_eq_abs]; calc
        _ = 2*|s|^2*dist x y := by ring
        _ = _ := by rw [sq_abs]

namespace OracleCompiler.Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {q : ℕ}

def affineReplies (s : ℝ) (H : Transcript d q) : Transcript d q :=
  fun i => ((H i).1,s • (H i).2)

lemma measurable_affineReplies (s : ℝ) : Measurable (affineReplies (d:=d) (q:=q) s) := by
  unfold affineReplies
  fun_prop

@[simp] lemma affineReplies_zero (s : ℝ) : affineReplies (d:=d) (q:=q) s 0=0 := by
  ext i <;> simp [affineReplies]

lemma affineReplies_update (s : ℝ) (H : Transcript d q) (i : Fin q) (u : Reply d) :
    affineReplies s (Function.update H i u)=
      Function.update (affineReplies s H) i (u.1,s • u.2) := by
  funext j
  by_cases hj : j=i
  · subst j; simp [affineReplies]
  · simp [affineReplies,Function.update_of_ne hj]

def affineOracle (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a) (s : ℝ) :
    Program Ω d q O where
  query i p := a p.1+s • A.query i (p.1,affineReplies s p.2)
  query_measurable i := (ha.comp measurable_fst).add
    (((A.query_measurable i).comp (measurable_fst.prodMk
      ((measurable_affineReplies s).comp measurable_snd))).const_smul s)
  output p := A.output (p.1,affineReplies s p.2)
  output_measurable := A.output_measurable.comp (measurable_fst.prodMk
    ((measurable_affineReplies s).comp measurable_snd))

lemma affineOracle_history (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a)
    (s : ℝ) {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) (ω : Ω) (n : ℕ) :
    affineReplies s ((A.affineOracle a ha s).history V ω n)=
      A.history (affinePotential V (a ω) s) ω n := by
  induction n with
  | zero => exact affineReplies_zero s
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [affineReplies_update,ih]
      congr 1
      change (V (a ω+s • A.query ⟨n,hn⟩ (ω,affineReplies s ((A.affineOracle a ha s).history V ω n))),
        s • gradient V (a ω+s • A.query ⟨n,hn⟩ (ω,affineReplies s ((A.affineOracle a ha s).history V ω n))))=_
      rw [ih]
      simp only [firstOrderReply,affinePotential,gradient_affinePotential hV]
    · exact ih

lemma affineOracle_run (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a)
    (s : ℝ) {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) (ω : Ω) :
    (A.affineOracle a ha s).run V ω=A.run (affinePotential V (a ω) s) ω := by
  unfold run
  change A.output (ω,affineReplies s ((A.affineOracle a ha s).history V ω q))=_
  rw [affineOracle_history A a ha s hV]

end OracleCompiler.Program
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ}

lemma gaussian_inner_law (a : Point d) :
    (stdGaussian (Point d)).map (fun z => inner ℝ a z)=
      gaussianReal 0 (‖a‖₊^2) := by
  simp only [←innerSL_apply_apply ℝ]
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Point d)) (innerSL ℝ a)
  simpa only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,Real.toNNReal_pow (norm_nonneg a),norm_toNNReal] using h

lemma gaussian_exp_inner_integrable (a : Point d) (t : ℝ) :
    Integrable (fun z => Real.exp (t*inner ℝ a z)) (stdGaussian (Point d)) := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := ‖a‖₊^2) t
  rw [←gaussian_inner_law a] at h
  exact h.comp_measurable (by fun_prop)

lemma gaussian_exp_inner_integral (a : Point d) (t : ℝ) :
    (∫z,Real.exp (t*inner ℝ a z) ∂stdGaussian (Point d))=
      Real.exp (‖a‖^2*t^2/2) := by
  have hlaw : HasLaw (fun z => inner ℝ a z) (gaussianReal 0 (‖a‖₊^2))
      (stdGaussian (Point d)) := ⟨by fun_prop,gaussian_inner_law a⟩
  simpa only [mgf,zero_mul,zero_add,NNReal.coe_pow,coe_nnnorm] using
    mgf_gaussianReal hlaw t

def gaussianShiftRatio (a z : Point d) : ℝ :=
  Real.exp (inner ℝ a z-‖a‖^2/2)

lemma gaussianShiftRatio_integrable (a : Point d) :
    Integrable (gaussianShiftRatio a) (stdGaussian (Point d)) := by
  change Integrable (fun z => Real.exp (inner ℝ a z-‖a‖^2/2)) _
  have h := (gaussian_exp_inner_integrable a 1).mul_const (Real.exp (-‖a‖^2/2))
  simpa only [one_mul,←Real.exp_add,sub_eq_add_neg,neg_div] using h

lemma gaussianShiftRatio_integral (a : Point d) :
    (∫z,gaussianShiftRatio a z ∂stdGaussian (Point d))=1 := by
  simp only [gaussianShiftRatio,sub_eq_add_neg,Real.exp_add]
  rw [integral_mul_const]
  have h := gaussian_exp_inner_integral a 1
  simp only [one_mul,one_pow,mul_one] at h
  rw [h,←Real.exp_add]
  simp

lemma gaussianShiftRatio_density (a : Point d) :
    (stdGaussian (Point d)).map (fun z => a+z)=
      (stdGaussian (Point d)).withDensity (fun z => ENNReal.ofReal (gaussianShiftRatio a z)) := by
  let e := (Homeomorph.addLeft a).toMeasurableEquiv
  have hpres : MeasurePreserving e (volume : Measure (Point d)) volume :=
    measurePreserving_add_left volume a
  rw [EulerDensity.standard_density,Measure.map_smul _ (by fun_prop),withDensity_smul_measure]
  change _ • Measure.map e _ = _
  rw [map_withDensity_of_measurePreserving e hpres (by fun_prop)]
  rw [←withDensity_mul _ (by fun_prop) (by unfold gaussianShiftRatio; fun_prop)]
  congr 2
  funext z
  change ENNReal.ofReal (Real.exp (-‖(-a)+z‖^2/2)) = _
  simp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,gaussianShiftRatio,←Real.exp_add]
  congr 2
  rw [show -a+z=z-a by abel,norm_sub_sq_real,real_inner_comm z a]
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma TVAtMost_of_density {f : E → ℝ} (hf : Integrable f μ) (hpos : ∀x,0≤f x) :
    TVAtMost (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ (∫x,|f x-1| ∂μ) := by
  intro s hs
  have hmeasure : (μ.withDensity (fun x => ENNReal.ofReal (f x))).real s=∫x in s,f x ∂μ := by
    rw [measureReal_def,withDensity_apply _ hs]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
      hf.aestronglyMeasurable.restrict).symm
  rw [hmeasure,←show (∫x in s,(1:ℝ) ∂μ)=μ.real s by simp,←integral_sub hf.restrict (integrable_const _)]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (hf.sub (integrable_const _)).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

lemma density_root_L1_sq {h : E → ℝ} (hh : MemLp h 2 μ)
    (hpos : ∀x,0≤h x) (hunit : (∫x,(h x)^2 ∂μ)=1) :
    (∫x,|(h x)^2-1| ∂μ)^2 ≤ 4*(1-(∫x,h x ∂μ)^2) := by
  have hi := hh.integrable (by norm_num : (1:ENNReal)≤2)
  have hsq := (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mp hh
  have hc := integral_mul_sq_le (hh.sub (memLp_const (1:ℝ))).norm
    (hh.add (memLp_const (1:ℝ)))
  have hmul : (fun x => |h x-1| *(h x+1))=(fun x => |(h x)^2-1|) := by
    funext x
    rw [←abs_of_nonneg (add_nonneg (hpos x) zero_le_one),←abs_mul]
    congr 1
    ring
  have hmi : Integrable (fun x => (h x)^2-2*h x) μ := hsq.sub (hi.const_mul 2)
  have hpi : Integrable (fun x => (h x)^2+2*h x) μ := hsq.add (hi.const_mul 2)
  have hminus : (∫x,(h x-1)^2 ∂μ)=2-2*(∫x,h x ∂μ) := by
    simp_rw [show ∀x,(h x-1)^2=(h x)^2-2*h x+1 by intro x; ring]
    rw [integral_add hmi (integrable_const _),
      integral_sub hsq (hi.const_mul 2),integral_const_mul,hunit]
    simp
    ring
  have hplus : (∫x,(h x+1)^2 ∂μ)=2+2*(∫x,h x ∂μ) := by
    simp_rw [show ∀x,(h x+1)^2=(h x)^2+2*h x+1 by intro x; ring]
    rw [integral_add hpi (integrable_const _),
      integral_add hsq (hi.const_mul 2),integral_const_mul,hunit]
    simp
    ring
  simp only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,sq_abs] at hc
  rw [hmul,hminus,hplus] at hc
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ}

lemma gaussian_shift_L1 (a : Point d) :
    (∫z,|gaussianShiftRatio a z-1| ∂stdGaussian (Point d))≤‖a‖ := by
  let h : Point d → ℝ := fun z => Real.exp ((inner ℝ a z-‖a‖^2/2)/2)
  have hs (z : Point d) : (h z)^2=gaussianShiftRatio a z := by
    dsimp [h,gaussianShiftRatio]
    rw [sq,←Real.exp_add]
    congr 1
    ring
  have hM : MemLp h 2 (stdGaussian (Point d)) := by
    apply (memLp_two_iff_integrable_sq (by dsimp [h]; fun_prop)).mpr
    simpa only [hs] using gaussianShiftRatio_integrable a
  have hi : (∫z,h z ∂stdGaussian (Point d))=Real.exp (-‖a‖^2/8) := by
    have he : h=fun z => Real.exp ((1/2)*inner ℝ a z)*Real.exp (-‖a‖^2/4) := by
      funext z
      dsimp [h]
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he,integral_mul_const,gaussian_exp_inner_integral,←Real.exp_add]
    congr 1
    ring
  have hb := density_root_L1_sq hM (fun z => (Real.exp_pos _).le)
    (by simpa only [hs] using gaussianShiftRatio_integral a)
  simp only [hs,hi] at hb
  have he : (Real.exp (-‖a‖^2/8))^2=Real.exp (-‖a‖^2/4) := by
    rw [sq,←Real.exp_add]
    congr 1
    ring
  rw [he] at hb
  have ht := Real.add_one_le_exp (-‖a‖^2/4)
  have hn : 0≤(∫z,|gaussianShiftRatio a z-1| ∂stdGaussian (Point d)) :=
    integral_nonneg (fun z => abs_nonneg (gaussianShiftRatio a z-1))
  nlinarith [norm_nonneg a]

theorem TVAtMost_gaussian_shift (a : Point d) :
    TVAtMost ((stdGaussian (Point d)).map (fun z => a+z))
      (stdGaussian (Point d)) ‖a‖ := by
  rw [gaussianShiftRatio_density]
  intro s hs
  exact (TVAtMost_of_density (gaussianShiftRatio_integrable a)
    (fun z => (Real.exp_pos _).le) s hs).trans (gaussian_shift_L1 a)

lemma TVAtMost.mono {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    {a b : ℝ} (h : TVAtMost μ ν a) (hab : a≤b) : TVAtMost μ ν b :=
  fun s hs => (h s hs).trans hab

lemma TVAtMost.symm {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    {a : ℝ} (h : TVAtMost μ ν a) : TVAtMost ν μ a := by
  intro s hs
  simpa only [abs_sub_comm] using h s hs

lemma TVAtMost.trans {E : Type*} [MeasurableSpace E] {μ ν θ : Measure E}
    {a b : ℝ} (h : TVAtMost μ ν a) (h' : TVAtMost ν θ b) : TVAtMost μ θ (a+b) := by
  intro s hs
  exact (abs_sub_le (μ.real s) (ν.real s) (θ.real s)).trans (add_le_add (h s hs) (h' s hs))

theorem TVAtMost_gaussian_affine (x y : Point d) {s : ℝ} (hs : 0<s) :
    TVAtMost ((stdGaussian (Point d)).map (fun z => x+s • z))
      ((stdGaussian (Point d)).map (fun z => y+s • z)) (‖x-y‖/s) := by
  have h := (TVAtMost_gaussian_shift (s⁻¹ • (x-y))).map
    (show Measurable (fun z : Point d => y+s • z) by fun_prop)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have he : (fun z : Point d => y+s • (s⁻¹ • (x-y)+z))=(fun z => x+s • z) := by
    funext z
    rw [smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    abel
  simpa only [Function.comp_def,he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,div_eq_inv_mul] using h
end LogConcaveSampling

end

end

end OAI

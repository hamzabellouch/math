import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellExpansion
import OAI.Probability.Perceptron.Cascade.CavityRPCControl

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma cavity_vector_residual (n : ℕ) (a h : ℝ) (hh : 2*h≤a) (x : Spin (n+1)) :
    (∫ y,sphericalExp n (x+Real.sqrt (a-2*h) •y) (Real.sqrt (n+1:ℕ))
      ∂stdGaussian (Spin (n+1)))=
      Real.exp ((n+1:ℕ)*(a-2*h)/2)*sphericalExp n x (Real.sqrt (n+1:ℕ)) := by
  rw [sphericalExp_gaussian_average,Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ)),
    Real.sq_sqrt (sub_nonneg.mpr hh)]

theorem cavity_finiteRPC_value (n d k : ℕ) (w h : Fin (k+1)→ℝ)
    (q : Fin (k+1)→Time) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh0 : 0≤h 0) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (c a : ℝ) :
    (n+1:ℕ)*(c+a-2*h (Fin.last k))/2+
    (∫ b, (∫ η,Real.log (decoratedTerminalTotal
      (cavityRPCStep n d (stepFieldIncrement k h)
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
      (cavityRPCTerminal n d
        (g.heatLog ⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ 1).f) k
      (cavityRPCRootState n d (Real.sqrt (2*h 0)) (Real.sqrt (q 0:ℝ)) b,η)/
      decoratedTerminalTotal
        (cavityRPCStep n d (stepFieldIncrement k h)
          (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
        (fun _=>0) k
      (cavityRPCRootState n d (Real.sqrt (2*h 0)) (Real.sqrt (q 0:ℝ)) b,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k (stepCumulative w))
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
    (n+1:ℕ)*((c+a)/2+finiteSphericalFieldValue n k w h)+
      d*controlValue P g.f (weightedStepTrial w q (fun i=>(hw i).le) hw1) := by
  rw [cavity_finiteRPC_roots n d k _ _ _ _ (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)]
  rw [cavityScalarRootValue_control k w q (fun i=>(hw i).le) hw1 hq
    (stepCumulative_pos w hw) g P hB]
  have he:=finiteAmplitudeSphereValue_fieldAmplitudes n k w h hh0
  unfold finiteAmplitudeSphereValue at he
  rw [fieldAmplitudes_increment,fieldAmplitudes_last] at he
  rw [he]
  ring

lemma gaussianBlockJoin_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockJoin N L)
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L)))
      (stdGaussian (Spin (N+L))) := by
  refine ⟨gaussianBlockJoin_measurable N L,?_⟩
  rw [←(gaussianBlockSplit_preserving N L).map_eq,
    Measure.map_map (gaussianBlockJoin_measurable N L) (gaussianBlockSplit_measurable N L)]
  simp only [Function.comp_def,gaussianBlockJoin_split]
  exact Measure.map_id

lemma stdGaussian_ofLp_preserving (N : ℕ) :
    MeasurePreserving (WithLp.ofLp : Spin N→Fin N→ℝ) (stdGaussian (Spin N))
      (Measure.pi fun _=>gaussianReal 0 1) := by
  refine ⟨(PiLp.continuous_ofLp 2 _).measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,
    Measure.map_map (PiLp.continuous_ofLp 2 _).measurable (PiLp.continuous_toLp 2 _).measurable]
  exact Measure.map_id

lemma cavityJoinedPatterns_preserving (N L M : ℕ) :
    MeasurePreserving (fun p : (Fin M→Fin N→ℝ)×(Fin M→Spin L)=>
      cavityJoinedPatterns N L M p.1 p.2)
      ((Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
      (Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1) := by
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hj := (stdGaussian_ofLp_preserving (N+L)).comp
    ((gaussianBlockJoin_preserving N L).comp (ht.prod (MeasurePreserving.id _)))
  have hp := measurePreserving_pi (fun _ : Fin M=>(Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
      (stdGaussian (Spin L))) (fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1)
      (fun _=>hj)
  have hr := (measurePreserving_arrowProdEquivProdArrow (Fin N→ℝ) (Spin L) (Fin M)
    (fun _=>Measure.pi fun _=>gaussianReal 0 1) (fun _=>stdGaussian (Spin L))).symm
  convert hp.comp hr using 1
  funext p i j
  rfl

lemma cavity_log_uniform_change {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {F G : S→ℝ}
    (hF : Measurable F) (hG : Measurable G) {A E : ℝ} (hA : 0≤A)
    (hFA : ∀ s,|F s|≤A) (hE : ∀ s,|F s-G s|≤E) :
    |Real.log (∫ s,Real.exp (F s) ∂μ)-Real.log (∫ s,Real.exp (G s) ∂μ)|≤E := by
  have hGA (s : S) : |G s|≤A+|E| := by
    calc
      _=|G s-F s+F s| := by ring_nf
      _≤|G s-F s|+|F s| := abs_add_le _ _
      _≤|E|+A := add_le_add ((show |G s-F s|≤E by simpa only [abs_sub_comm] using hE s).trans (le_abs_self E)) (hFA s)
      _=A+|E| := add_comm _ _
  have hFi : Integrable (fun s=>Real.exp (F s)) μ := by
    apply Integrable.of_bound hF.exp.aestronglyMeasurable (Real.exp A)
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hFA s))
  have hGi : Integrable (fun s=>Real.exp (G s)) μ := by
    apply Integrable.of_bound hG.exp.aestronglyMeasurable (Real.exp (A+|E|))
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hGA s))
  exact abs_log_integral_exp_sub_le μ hFi hGi
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hF hA hFA 1)
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hG (by positivity) hGA 1) hE

lemma cavityShellTaylorModel_measurable (n L M : ℕ) (f : Jet3)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) :
    Measurable (cavityShellTaylorModel n L M f a y) := by
  have h0 := f.f.continuous.measurable
  have h1 := f.d1.continuous.measurable
  have h2 := f.d2.continuous.measurable
  unfold cavityShellTaylorModel normalizedPatternEnergy cavityLinearField cavityQuadraticField bulkC
  fun_prop

theorem cavity_true_shell_log_expansion (n L M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*(L+1)≤n+1)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (v : ℕ→ℝ) (g : BulkMark (n+1)) :
    |Real.log (∫ s,Real.exp (cavityShellPatternEnergy n L M f.f
        (cavityJoinedPatterns (n+1) L M a y) s+inner ℝ (bulkFeature (n+1) v s.1) g)
          ∂cavityShellBaseLaw n L)-
      Real.log (∫ s,Real.exp (cavityShellTaylorModel n L M f a y s+
        inner ℝ (bulkFeature (n+1) v s.1) g) ∂cavityShellBaseLaw n L)|≤
      ∑ i,cavityRemainderMajorant (cavityRemainderCoefficients f h1 h2 h3 L (L+1)) (n+1:ℕ) ‖y i‖ := by
  let := cavityShellBaseLaw_probability n L hp
  have hm : Measurable (fun s : CavityShellSpin n L=>inner ℝ (bulkFeature (n+1) v s.1) g) :=
    (((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst).inner measurable_const)
  apply cavity_log_uniform_change (cavityShellBaseLaw n L)
    ((cavityShellPatternEnergy_measurable n L M f.f _).add hm)
    ((cavityShellTaylorModel_measurable n L M f a y).add hm)
    (A:=M*‖f.f‖+bulkFeatureBound (n+1) v*‖g‖)
    (add_nonneg (by positivity) (mul_nonneg (by unfold bulkFeatureBound; positivity) (norm_nonneg _)))
  · intro s
    apply (abs_add_le _ _).trans
    apply add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
    simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) g
  · intro s
    simpa only [Pi.add_apply,add_sub_add_right_eq_sub] using cavity_true_shell_expansion n L M f h1 h2 h3 hn a y s

end SphericalPerceptronFreeEnergy
end

end OAI

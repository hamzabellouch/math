import OAI.Probability.InvariantIsing.Fields.FieldBounds
import OAI.Probability.IsingPerceptron.CascadePair

namespace OAI

/-!
The finite-depth Gaussian marking input used in the one-site functional.
The logarithmic terminal is unbounded; the linear-growth cascade theorem
supplies its integrability. This is the Gaussian specialization of
Bolthausen--Sznitman (1998), Appendix Proposition A.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma integral_gaussianReal_zero_eq_standard (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ g, F g ∂gaussianReal 0 v) =
      ∫ g, F (Real.sqrt (v : ℝ) * g) ∂gaussianReal 0 1 := by
  have hm : (gaussianReal 0 1).map (fun g => Real.sqrt (v : ℝ) * g) =
      gaussianReal 0 v := by
    convert! gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (v : ℝ)) using 1
    simp only [mul_zero, mul_one]
    congr 1
    ext
    simp only [NNReal.coe_mk, Real.sq_sqrt v.coe_nonneg]
  rw [← hm]
  exact integral_map
    (show AEMeasurable (fun g : ℝ => Real.sqrt (v : ℝ) * g) (gaussianReal 0 1) from
      (measurable_id.const_mul _).aemeasurable) hF.aestronglyMeasurable

lemma gaussianOperator_eq_gaussian_logMean {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0)
    {F : ℝ → ℝ} (hF : Measurable F) (x : ℝ) :
    gaussianOperator a v F x =
      IsingPerceptron.logMean a (gaussianReal 0 v) (fun g => F (x + g)) := by
  simp only [gaussianOperator, ha, ite_false, IsingPerceptron.logMean]
  have hm : Measurable (fun g : ℝ => Real.exp (a * F (x + g))) :=
    (((hF.comp (measurable_const.add measurable_id)).const_mul a).exp)
  rw [integral_gaussianReal_zero_eq_standard v hm]
  ring

lemma gaussianCascadeRecursion_eq_fold (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, b i ≠ 0) {F : ℝ → ℝ} (hF : Measurable F) :
    IsingPerceptron.cascadeRecursion n b
      (fun i => ⟨gaussianReal 0 (v i), inferInstance⟩)
      (fun _ p => p.1 + p.2) F =
      (List.ofFn (fun i : Fin n => (b i, (v i : ℝ)))).foldr
        (fun av U => gaussianOperator av.1 av.2 U) F := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have ht := IsingPerceptron.measurable_cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ => measurable_fst.add measurable_snd) hF
    have he := ih (fun i => b (i + 1)) (fun i => v (i + 1))
      (fun i hi => hb (i + 1) (by omega))
    change Measurable (IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ p => p.1 + p.2) F) at ht
    rw [he] at ht
    rw [List.ofFn_succ, List.foldr_cons]
    funext x
    change IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
      (fun g => IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
        (fun i => ⟨gaussianReal 0 (v (i + 1)), inferInstance⟩)
        (fun _ p => p.1 + p.2) F (x + g)) = _
    rw [he]
    exact (gaussianOperator_eq_gaussian_logMean (hb 0 (by omega)) (v 0) ht x).symm

def gaussianCascadeLaw (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) :
    Measure (IsingPerceptron.NoiseTree ℝ n) :=
  IsingPerceptron.noiseCascadeLaw ℝ n b
    (fun i => ⟨gaussianReal 0 (v i), inferInstance⟩)

def gaussianCascadeLog (n : ℕ) (x : ℝ) (T : IsingPerceptron.NoiseTree ℝ n) : ℝ :=
  Real.log (∫ leaf, Real.exp (IsingPerceptron.noiseLeafTerminal n
    (fun _ z => Real.log (Real.cosh z)) (fun _ p => p.1 + p.2) x leaf)
    ∂IsingPerceptron.noiseLeafKernel ℝ n T)

/-- Exact finite Gaussian marking recursion, with the integrability needed
to take the outer expectation. No boundedness of `log cosh` is assumed. -/
theorem gaussianCascadeLog_recursion (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (x : ℝ) :
    Integrable (gaussianCascadeLog n x) (gaussianCascadeLaw n b v) ∧
      (∫ T, gaussianCascadeLog n x T ∂gaussianCascadeLaw n b v) =
        ((List.ofFn (fun i : Fin n => (b i, (v i : ℝ)))).foldr
          (fun av U => gaussianOperator av.1 av.2 U)
          (fun z => Real.log (Real.cosh z))) x := by
  have h := IsingPerceptron.gaussian_logCosh_cascade n b hb (fun _ => 0) v x
  have he := IsingPerceptron.noise_leaf_log_eq_ratio n b hb
    (fun i => (⟨gaussianReal 0 (v i), inferInstance⟩ : ProbabilityMeasure ℝ))
    (fun _ => measurable_fst.add measurable_snd) IsingPerceptron.measurable_logCosh x
  refine ⟨h.1.congr (Filter.EventuallyEq.symm he), ?_⟩
  calc
    _ = _ := integral_congr_ae he
    _ = _ := h.2.1
    _ = _ := congrFun (gaussianCascadeRecursion_eq_fold n b v
      (fun i hi => (hb.1 i hi).1.ne') IsingPerceptron.measurable_logCosh) x

end InvariantIsing

end

end OAI

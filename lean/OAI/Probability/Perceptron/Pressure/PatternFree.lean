import Mathlib
import OAI.Probability.Perceptron.Variational.DensityDerivative
import OAI.Probability.Perceptron.Variational.StepDual
import OAI.Probability.Perceptron.Cascade.CascadeHeat

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def enrichedSpinProjection (N : ℕ) (p : Fin N→ℕ) : EnrichedMark N N p →L[ℝ] Spin N :=
  ({ toFun := fun a => WithLp.toLp 2 (fun i => a (.inl i))
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : EnrichedMark N N p →ₗ[ℝ] Spin N).toContinuousLinearMap

@[simp] lemma enrichedSpinProjection_apply (N : ℕ) (p : Fin N→ℕ)
    (a : EnrichedMark N N p) (i : Fin N) : enrichedSpinProjection N p a i=a (.inl i) := rfl

lemma enrichedSpinProjection_preserving (N : ℕ) (p : Fin N→ℕ) :
    MeasurePreserving (enrichedSpinProjection N p) (stdGaussian (EnrichedMark N N p))
      (stdGaussian (Spin N)) := by
  refine ⟨(enrichedSpinProjection N p).measurable,?_⟩
  have hi : (Measure.pi (fun _ : EnrichedIndex N N p => gaussianReal 0 1)).map
      (fun a i => a (Sum.inl i))=Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : EnrichedIndex N N p => gaussianReal 0 1)
        (f := (Sum.inl : Fin N→EnrichedIndex N N p)) Sum.inl_injective)
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : EnrichedIndex N N p => gaussianReal 0 1)).map
    ((WithLp.toLp 2) ∘ (fun a i => a (Sum.inl i)))=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),hi,map_pi_eq_stdGaussian]

section Transport
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [BorelSpace E] in
lemma gaussianLinearBackward_projection (P : E →L[ℝ] F)
    (hp : MeasurePreserving P (stdGaussian E) (stdGaussian F))
    (A : ℕ→E →L[ℝ] E) (σ : ℕ→ℝ) (hA : ∀ j x, P (A j x)=σ j • P x)
    {f : F→ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k→ℝ) (hz : ∀ i, 0≤z i) (x : E) :
    gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) (fun a => f (P a)) x=
      gaussianBackward (stdGaussian F) (cascadeHeatWord σ k z) f (P x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord,gaussianLinearBackward,cascadeHeatWord,gaussianBackward,
      gaussianLinearEntropic,gaussianEntropic]
    simp_rw [ih (fun i => z i.succ) (fun i => hz i.succ),map_add,hA]
    let g := gaussianBackward (stdGaussian F) (cascadeHeatWord σ k (fun i => z i.succ)) f
    have hg : Continuous g := (gaussianBackward_lipschitz (stdGaussian F) hf _
      (cascadeHeatWord_nonneg σ k _ (fun i => hz i.succ))).continuous
    have hc : cgf (fun y => g (P x+σ k • P y)) (stdGaussian E)=
        cgf (fun y => g (P x+σ k • y)) (stdGaussian F) := by
      funext t
      unfold cgf mgf
      rw [← hp.map_eq,integral_map hp.measurable.aemeasurable (by
        exact (Real.continuous_exp.comp (continuous_const.mul
          (hg.comp (continuous_const.add (continuous_const.smul continuous_id))))).aestronglyMeasurable)]
    exact congrArg (fun c : ℝ→ℝ => ∫ t in (0:ℝ)..1, deriv c (z 0*t)) hc
end Transport

lemma enrichedSpinProjection_increment {N k : ℕ} (p d : Fin N→ℕ)
    (h : Fin (k+1)→ℝ) (j : ℕ) (a : EnrichedMark N N p) :
    enrichedSpinProjection N p (enrichedIncrementMap p d h j a)=
      stepFieldIncrement k h j • enrichedSpinProjection N p a := by
  ext i
  by_cases hj : j<k
  · simp only [enrichedIncrementMap,dite_eq_left hj,enrichedSpinProjection_apply,diagonalMark_apply,
      enrichedCoordinateLevel,stepFieldIncrement,PiLp.smul_apply,smul_eq_mul]
    congr 2
    have h₁ : (⟨k-j,by omega⟩ : Fin (k+1))=(Fin.rev ⟨j,hj⟩).succ := by
      ext; simp only [Fin.val_succ,Fin.val_rev]; omega
    have h₀ : (⟨k-j-1,by omega⟩ : Fin (k+1))=(Fin.rev ⟨j,hj⟩).castSucc := by
      ext; simp only [Fin.val_castSucc,Fin.val_rev]; omega
    rw [h₁,h₀]
    ring
  · simp [enrichedIncrementMap,stepFieldIncrement,hj]

lemma enrichedSpinProjection_root {N k : ℕ} (p d : Fin N→ℕ)
    (h : Fin (k+1)→ℝ) (a : EnrichedMark N N p) :
    enrichedSpinProjection N p (enrichedRootMap p d h a)=
      Real.sqrt (2*h 0) • enrichedSpinProjection N p a := by ext; rfl

lemma enrichedTerminal_patternFree (n : ℕ) (f : ℝ →ᵇ ℝ) (g : Fin 0→Fin (n+1)→ℝ)
    (p : Fin (n+1)→ℕ) (htop : ℝ) (a : EnrichedMark (n+1) (n+1) p) :
    enrichedTerminal n 0 f g p (fun _ => 0) htop a=
      logSphericalExp n (Real.sqrt (n+1:ℕ)) (enrichedSpinProjection (n+1) p a)-(n+1:ℕ)*htop := by
  unfold enrichedTerminal vectorLogPartition vectorPartition logSphericalExp sphericalExp
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    apply congrArg Real.exp
    simp only [normalizedPatternEnergy,Finset.univ_eq_empty,Finset.sum_empty,zero_add,
      sourceEnrichedFeature,innerSL_apply_apply,PiLp.inner_apply,enrichedFeature,
      Fintype.sum_sum_type,perturbationAmplitude,mul_zero,
      inner_zero_left,zero_mul,Finset.sum_const_zero,add_zero,enrichedSpinProjection_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change a (.inl i)*(Real.sqrt (n+1:ℕ)*x.val i)=
      Real.sqrt (n+1:ℕ)*(x.val i*a (.inl i))
    ring

lemma enrichedExpectedLog_patternFree (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin 0→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    enrichedExpectedLog n 0 k f p d (fun _ => 0) h z g=
      (n+1:ℕ)*amplitudeSphereValue n k (stepFieldIncrement k h) z (Real.sqrt (2*h 0))-
        (n+1:ℕ)*h (Fin.last k) := by
  let F := logSphericalExp n (Real.sqrt (n+1:ℕ))
  let c := -((n+1:ℕ)*h (Fin.last k))
  have hF : LipschitzWith ⟨|Real.sqrt (n+1:ℕ)|,abs_nonneg _⟩ F :=
    logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))
  have hFc : LipschitzWith ⟨|Real.sqrt (n+1:ℕ)|,abs_nonneg _⟩ (fun a => F a+c) := by
    intro a b
    simpa only [F,edist_add_right] using hF a b
  have hp := enrichedSpinProjection_preserving (n+1) p
  have hG := gaussianBackward_lipschitz (stdGaussian (Spin (n+1))) hF _
    (cascadeHeatWord_nonneg (stepFieldIncrement k h) k z (fun i => (hz0 i).le))
  have hroot : Continuous (fun a : Spin (n+1) =>
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord (stepFieldIncrement k h) k z)
        F (Real.sqrt (2*h 0) • a)) := hG.continuous.comp (show Continuous (fun a : Spin (n+1) => Real.sqrt (2*h 0) • a) by fun_prop)
  unfold enrichedExpectedLog
  rw [(enrichedCascadeLog_joint_mean n 0 k f g p d (fun _ => 0) h z hz hz0 hz1).2]
  have ht : enrichedTerminal n 0 f g p (fun _ => 0) (h (Fin.last k))=
      (fun a => F (enrichedSpinProjection (n+1) p a)+c) := by
    funext a
    exact enrichedTerminal_patternFree n f g p (h (Fin.last k)) a
  rw [ht]
  change (∫ a, gaussianLinearBackward (stdGaussian (EnrichedMark (n+1) (n+1) p))
    (linearCascadeWord (enrichedIncrementMap p d h) k z)
    (fun a => F (enrichedSpinProjection (n+1) p a)+c) (enrichedRootMap p d h a)
      ∂stdGaussian (EnrichedMark (n+1) (n+1) p))=_
  simp_rw [gaussianLinearBackward_projection (enrichedSpinProjection (n+1) p) hp
    (enrichedIncrementMap p d h) (stepFieldIncrement k h) (enrichedSpinProjection_increment p d h)
    hFc k z (fun i => (hz0 i).le),enrichedSpinProjection_root,
    gaussianBackward_add_const (stdGaussian (Spin (n+1))) hF _
      (cascadeHeatWord_nonneg (stepFieldIncrement k h) k z (fun i => (hz0 i).le)) c]
  have hi : Integrable (fun a : Spin (n+1) =>
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord (stepFieldIncrement k h) k z)
        F (Real.sqrt (2*h 0) • a)) (stdGaussian (Spin (n+1))) :=
    ((lipschitz_memLp_stdGaussian (hG.comp ((Real.sqrt (2*h 0) • ContinuousLinearMap.id ℝ (Spin (n+1))).lipschitzWith)))).integrable (by norm_num)
  have hi' : Integrable (fun a : EnrichedMark (n+1) (n+1) p =>
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord (stepFieldIncrement k h) k z)
        F (Real.sqrt (2*h 0) • enrichedSpinProjection (n+1) p a))
      (stdGaussian (EnrichedMark (n+1) (n+1) p)) := by
    convert ((hp.integrable_comp hroot.aestronglyMeasurable).mpr hi) using 1
    rfl
  rw [integral_add hi' (integrable_const c),
    integral_const,probReal_univ,one_smul]
  have he : (∫ a, gaussianBackward (stdGaussian (Spin (n+1)))
      (cascadeHeatWord (stepFieldIncrement k h) k z) F (Real.sqrt (2*h 0) • enrichedSpinProjection (n+1) p a)
      ∂stdGaussian (EnrichedMark (n+1) (n+1) p))=
        (∫ a, gaussianBackward (stdGaussian (Spin (n+1)))
      (cascadeHeatWord (stepFieldIncrement k h) k z) F (Real.sqrt (2*h 0) • a)
      ∂stdGaussian (Spin (n+1))) := by
    have hm := integral_map (μ := stdGaussian (EnrichedMark (n+1) (n+1) p))
      hp.measurable.aemeasurable hroot.aestronglyMeasurable
    rw [hp.map_eq] at hm
    exact hm.symm
  rw [he,amplitudeSphereValue_eq_backward n k _ z hz hz0 hz1,
    gaussianBackward,gaussianEntropic_zero _ hG]
  simp only [zero_add]
  dsimp only [F,c]
  field_simp
  ring

lemma sourceCountExpectedLog_patternFree (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w h : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0≤h 0) :
    (1/(n+1:ℕ))*sourceCountExpectedLog n k f p d h (stepCumulative w) (fun _ => 0) 0=
      finiteSphericalFieldValue n k w h := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hi := (enrichedPoissonLog_section_variance n 0 k f p d (fun _ => 0) h
    (stepCumulative w) hz hz0 hz1).1.integrable (by norm_num)
  have he : sourceCountExpectedLog n k f p d h (stepCumulative w) (fun _ => 0) 0=
      ∫ g, enrichedExpectedLog n 0 k f p d (fun _ => 0) h (stepCumulative w)
        (patternPrefix (n+1) 0 g) ∂infinitePatternRowsLaw (n+1) := integral_prod _ hi
  rw [he]
  simp_rw [enrichedExpectedLog_patternFree n k f _ p d h (stepCumulative w) hz hz0 hz1]
  rw [integral_const,probReal_univ,one_smul,amplitudeSphereValue_eq]
  have hnonneg (index : Fin (k+1)) : 0≤2*h index :=
    mul_nonneg (by norm_num) (hh0.trans (hh (Fin.zero_le index)))
  have hs : (⟨(Real.sqrt (2*h 0))^2,sq_nonneg _⟩ : ℝ≥0)=Real.toNNReal (2*h 0) := by
    apply NNReal.eq
    change (Real.sqrt (2*h 0))^2=(Real.toNNReal (2*h 0):ℝ)
    rw [Real.sq_sqrt (hnonneg 0),Real.toNNReal_of_nonneg (hnonneg 0)]
    rfl
  rw [hs]
  unfold finiteSphericalFieldValue
  field_simp

lemma sourceExpectedPressure_patternFree (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w h : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0≤h 0) :
    sourceExpectedPressure n k f p d h (stepCumulative w) 0 (fun _ => 0)=
      finiteSphericalFieldValue n k w h := by
  rw [sourceExpectedPressure_poissonMean n k f p d h (stepCumulative w) (fun _ => 0)
    (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)]
  simp only [mul_zero,NNReal.coe_zero]
  simp only [poissonRealMean,neg_zero,Real.exp_zero,one_mul,zero_pow_eq,ite_div,zero_div,ite_mul,zero_mul]
  simp only [tsum_ite_eq,one_div,Nat.factorial_zero,Nat.cast_one,inv_one,one_mul]
  simpa only [one_div] using sourceCountExpectedLog_patternFree n k f p d w h hw hw1 hh hh0

end SphericalPerceptronFreeEnergy
end

end OAI

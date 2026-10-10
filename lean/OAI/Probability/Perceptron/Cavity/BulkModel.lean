import Mathlib
import OAI.Probability.Perceptron.Interpolation.GibbsOverlapArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def bulkScale (N : ℕ) : ℝ := (N:ℝ)^((3:ℝ)/8)
def bulkDegree {N : ℕ} (p : Fin N) : ℕ := p.val+1
abbrev BulkMark (N : ℕ) := EnrichedMark N N bulkDegree

def bulkAmplitude (N : ℕ) (v : ℕ → ℝ) (p : Fin N) : ℝ :=
  bulkScale N * (2:ℝ)^(-((p.val+1:ℕ):ℤ))*v (p.val+1)

def bulkFeature (N : ℕ) (v : ℕ → ℝ) : NormalizedSpin N → BulkMark N :=
  enrichedFeature N N bulkDegree 0 (bulkAmplitude N v)

def bulkCovariance (N : ℕ) (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Fin N, ((2:ℝ)^(-((p.val+1:ℕ):ℤ)))^2 * (v (p.val+1))^2 * r^(p.val+1)

def bulkHamiltonian (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin N → ℝ) (g : BulkMark N) (x : NormalizedSpin N) : ℝ :=
  normalizedPatternEnergy N M f a x + inner ℝ (bulkFeature N v x) g

def bulkLogPartition (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) : ℝ :=
  vectorLogPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f a)
    (fun x => innerSL ℝ (bulkFeature (n+1) v x)) g

def bulkDisorderLaw (N M : ℕ) : Measure ((Fin M → Fin N → ℝ) × BulkMark N) :=
  (Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))).prod (stdGaussian (BulkMark N))

instance bulkDisorderLaw_probability (N M : ℕ) : IsProbabilityMeasure (bulkDisorderLaw N M) := by
  unfold bulkDisorderLaw
  infer_instance

def bulkExpectedLog (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) : ℝ :=
  ∫ a, bulkLogPartition n M f v a.1 a.2 ∂bulkDisorderLaw (n+1) M

def bulkB (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) : ℝ :=
  (N:ℝ)⁻¹ * ∑ j, f.d1 (∑ i, a j i*x.val i) * f.d1 (∑ i, a j i*y.val i)

def bulkC (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x : NormalizedSpin N) : ℝ :=
  (N:ℝ)⁻¹ * ∑ j, (f.d2 (∑ i, a j i*x.val i) -
    (∑ i, a j i*x.val i)*f.d1 (∑ i, a j i*x.val i))

lemma bulkFeature_continuous (N : ℕ) (v : ℕ → ℝ) : Continuous (bulkFeature N v) :=
  enrichedFeature_continuous N N bulkDegree 0 (bulkAmplitude N v)

lemma bulkFeature_inner (N : ℕ) (v : ℕ → ℝ) (x y : NormalizedSpin N) :
    inner ℝ (bulkFeature N v x) (bulkFeature N v y) =
      bulkScale N ^ 2 * bulkCovariance N v (spinOverlap x y) := by
  rw [bulkFeature, enrichedFeature_inner]
  simp only [zero_pow two_ne_zero, zero_mul, zero_add, bulkCovariance, Finset.mul_sum,
    bulkAmplitude, bulkDegree]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bulkFeature_norm_sq (N : ℕ) (v : ℕ → ℝ) (x : NormalizedSpin N) :
    ‖bulkFeature N v x‖^2 = ∑ p, bulkAmplitude N v p^2 := by
  rw [bulkFeature, enrichedFeature_norm_sq]
  simp

lemma bulkLogPartition_eq (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) :
    bulkLogPartition n M f v a g =
      Real.log (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1) := by
  simp only [bulkLogPartition, vectorLogPartition, vectorPartition, tiltPartition, one_mul, bulkHamiltonian,
    innerSL_apply_apply]

lemma bulkB_bound (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) : |bulkB N M f a x y| ≤ (M:ℝ)/(N:ℝ)*‖f.d1‖^2 := by
  unfold bulkB
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    _ ≤ (N:ℝ)⁻¹ * ∑ _ : Fin M, ‖f.d1‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul, pow_two]
        exact mul_le_mul (f.d1.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _)
          (abs_nonneg _) (norm_nonneg _))
    _ = _ := by simp; ring

abbrev BulkDisorder (N M : ℕ) := (Fin M→Fin N→ℝ) × BulkMark N

def bulkFeatureBound (N : ℕ) (v : ℕ→ℝ) : ℝ := Real.sqrt (∑ p, bulkAmplitude N v p^2)

lemma bulkFeature_norm (N : ℕ) (v : ℕ→ℝ) (x : NormalizedSpin N) :
    ‖bulkFeature N v x‖=bulkFeatureBound N v := by
  rw [bulkFeature, enrichedFeature_norm]
  simp [bulkFeatureBound]

lemma bulkHamiltonian_continuous (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Continuous (fun p : BulkDisorder N M × NormalizedSpin N =>
      bulkHamiltonian N M f v p.1.1 p.1.2 p.2) := by
  unfold bulkHamiltonian
  exact ((normalizedPatternEnergy_continuous N M f).comp
    (continuous_fst.fst.prodMk continuous_snd)).add
    (((bulkFeature_continuous N v).comp continuous_snd).inner continuous_fst.snd)

lemma bulkHamiltonian_bound (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (a : BulkDisorder N M)
    (x : NormalizedSpin N) :
    |bulkHamiltonian N M f v a.1 a.2 x| ≤ M*‖f‖+bulkFeatureBound N v*‖a.2‖ := by
  apply (abs_add_le _ _).trans
  exact add_le_add (normalizedPatternEnergy_bound _ _ _ _ _) (by
    simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature N v x) a.2)

lemma bulkHamiltonian_exp_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    Integrable (fun x => Real.exp (bulkHamiltonian (n+1) M f v a.1 a.2 x)) (unitSphereLaw (n+1)) := by
  apply Integrable.of_bound
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable
    (Real.exp (M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖))
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (bulkHamiltonian_bound (n+1) M f v a x))

def bulkSpinKernel (n M : ℕ) : Kernel (BulkDisorder (n+1) M) (NormalizedSpin (n+1)) :=
  Kernel.const _ (unitSphereLaw (n+1))

instance bulkSpinKernel_markov (n M : ℕ) : IsMarkovKernel (bulkSpinKernel n M) := by
  unfold bulkSpinKernel; infer_instance

def bulkOverlap {N : ℕ} (x y : NormalizedSpin N) : CompactOverlap :=
  ⟨spinOverlap x y,abs_le.mp (spinOverlap_abs_le x y)⟩

lemma bulkOverlap_measurable (N : ℕ) : Measurable (Function.uncurry (bulkOverlap (N:=N))) := by
  apply Measurable.subtype_mk
  exact measurable_fst.subtype_val.inner measurable_snd.subtype_val

def bulkGibbsArrayLaw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    ProbabilityMeasure (CompactArray CompactOverlap) :=
  gibbsOverlapArrayLaw (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable bulkOverlap (bulkOverlap_measurable (n+1))

lemma bulkGibbsArray_block (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    (∫ R, F (compactBlock r R) ∂bulkGibbsArrayLaw n M f v) =
      ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
        (fun x => F (fun i j => bulkOverlap (x i) (x j))) ∂bulkDisorderLaw (n+1) M := by
  exact gibbsOverlapArray_block (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable _ (bulkOverlap_measurable (n+1))
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r F

end SphericalPerceptronFreeEnergy
end

end OAI

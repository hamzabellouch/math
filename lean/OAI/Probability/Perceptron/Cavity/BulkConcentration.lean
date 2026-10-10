import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeatureBound_sq (N : ℕ) (v : ℕ→ℝ) :
    bulkFeatureBound N v^2 = ∑ p, bulkAmplitude N v p^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma bulkFeatureBound_sq_le (N : ℕ) (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ p, |v (p+1)|≤C) : bulkFeatureBound N v^2 ≤ C^2*bulkScale N^2 := by
  rw [bulkFeatureBound_sq]
  have hi (p : Fin N) : bulkAmplitude N v p^2 ≤ C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := by
    let w : ℝ := (1/2:ℝ)^(p.val+1)
    have hw0 : 0≤w := pow_nonneg (by norm_num) _
    have hw1 : w≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv2 : v (p.val+1)^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v (p.val+1))) hC).2 (hv p.val)
    unfold bulkAmplitude
    rw [perturbationWeight_eq]
    change (bulkScale N*w*v (p.val+1))^2 ≤ _
    calc
      _ ≤ bulkScale N^2*w^2*C^2 := by
        rw [mul_pow,mul_pow]; exact mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ ≤ C^2*bulkScale N^2*w := by
        nlinarith [mul_le_mul_of_nonneg_left (show w^2≤w by nlinarith) (mul_nonneg (sq_nonneg C) (sq_nonneg (bulkScale N)))]
  calc
    _ ≤ ∑ p : Fin N, C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := Finset.sum_le_sum fun p _ => hi p
    _ = C^2*bulkScale N^2*(∑ p : Fin N, (1/2:ℝ)^(p.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*bulkScale N^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (by positivity)
    _ = _ := mul_one _

lemma bulkLogPartition_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) := by
  simp_rw [bulkLogPartition_eq]
  change Measurable (fun a : BulkDisorder (n+1) M => Real.log (∫ x,
    Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x) ∂unitSphereLaw (n+1)))
  simp only [one_mul]
  exact (bulkHamiltonian_continuous (n+1) M f v).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma bulkLogPartition_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    |bulkLogPartition n M f v a.1 a.2| ≤ M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖ := by
  apply vectorLogPartition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (normalizedPatternEnergy_bound (n+1) M f a.1)
  intro x
  simp only [Function.comp_apply,innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl]

lemma bulkLogPartition_memLp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    MemLp (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) 2
      (bulkDisorderLaw (n+1) M) := by
  have hi : MemLp (id : BulkMark (n+1) → BulkMark (n+1)) 2 (stdGaussian (BulkMark (n+1))) :=
    IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)
  have hn : MemLp (fun g : BulkMark (n+1) => ‖g‖) 2 (stdGaussian (BulkMark (n+1))) := hi.norm
  have hc : MemLp (fun _ : BulkMark (n+1) => (M:ℝ)*‖f‖) 2 (stdGaussian (BulkMark (n+1))) := memLp_const _
  have hg : MemLp (fun g : BulkMark (n+1) => M*‖f‖+bulkFeatureBound (n+1) v*‖g‖) 2
      (stdGaussian (BulkMark (n+1))) := hc.add (hn.const_mul (bulkFeatureBound (n+1) v))
  apply (hg.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulkLogPartition_measurable n M f v).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkLogPartition_bound n M f v a

lemma bulkLogPartition_variance (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    variance (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2)
      (bulkDisorderLaw (n+1) M) ≤ Real.pi^2/8*bulkFeatureBound (n+1) v^2+M*(2*‖f‖)^2 := by
  apply vectorLogPartition_mixed_variance (unitSphereLaw (n+1))
    (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) M
    (W := normalizedPatternEnergy (n+1) M f)
    (V := fun x => innerSL ℝ (bulkFeature (n+1) v x))
    (normalizedPatternEnergy_continuous (n+1) M f).measurable
    (fun x => (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_id.prodMk continuous_const))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (Real.sqrt_nonneg _) (normalizedPatternEnergy_bound (n+1) M f)
    (fun x => by simp only [innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl])
    (normalizedPatternEnergy_update (n+1) M f)


lemma enrichedFeature_cross_inner (N J : ℕ) (p : Fin J→ℕ) (c d : Fin J→ℝ)
    (x y : NormalizedSpin N) :
    inner ℝ (enrichedFeature N J p 0 c x) (enrichedFeature N J p 0 d y)=
      ∑ j, c j*d j*spinOverlap x y^(p j) := by
  change (∑ i : EnrichedIndex N J p,
    enrichedFeature N J p 0 d y i * enrichedFeature N J p 0 c x i)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedFeature,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [← spinTensorFeature_inner N (p j) x y]
  change (∑ i, d j*spinTensorFeature N (p j) y i*(c j*spinTensorFeature N (p j) x i))=
    c j*d j*(∑ i, spinTensorFeature N (p j) y i*spinTensorFeature N (p j) x i)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

def bulkDirection (N : ℕ) (p : Fin N) : NormalizedSpin N→BulkMark N :=
  enrichedFeature N N bulkDegree 0 (Pi.single (M := fun _ : Fin N => ℝ) p 1)

def bulkCoefficient (N : ℕ) (p : Fin N) : ℝ := bulkScale N*(2:ℝ)^(-((p.val+1:ℕ):ℤ))

def bulkY (N : ℕ) (p : Fin N) (g : BulkMark N) (x : NormalizedSpin N) : ℝ :=
  inner ℝ (bulkDirection N p x) g

lemma bulkDirection_continuous (N : ℕ) (p : Fin N) : Continuous (bulkDirection N p) :=
  enrichedFeature_continuous _ _ _ _ _

lemma bulkDirection_norm (N : ℕ) (p : Fin N) (x : NormalizedSpin N) : ‖bulkDirection N p x‖=1 := by
  rw [bulkDirection,enrichedFeature_norm]
  have he : (∑ j : Fin N, (Pi.single (M := fun _ : Fin N => ℝ) p (1:ℝ) j)^2)=1 := by
    classical
    simp [Pi.single_apply]
  rw [he]
  norm_num

lemma bulkDirection_inner (N : ℕ) (p : Fin N) (x y : NormalizedSpin N) :
    inner ℝ (bulkDirection N p x) (bulkDirection N p y)=spinOverlap x y^(p.val+1) := by
  simp only [bulkDirection]
  rw [enrichedFeature_cross_inner]
  classical
  simp [Pi.single_apply,bulkDegree]

lemma bulkFeature_direction_inner (N : ℕ) (v : ℕ→ℝ) (p : Fin N) (x y : NormalizedSpin N) :
    inner ℝ (bulkDirection N p x) (bulkFeature N v y)=
      bulkAmplitude N v p*spinOverlap x y^(p.val+1) := by
  rw [bulkDirection,bulkFeature,enrichedFeature_cross_inner]
  classical
  simp [Pi.single_apply,bulkDegree]

lemma bulkY_bound (N : ℕ) (p : Fin N) (g : BulkMark N) (x : NormalizedSpin N) : |bulkY N p g x|≤‖g‖ := by
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [bulkDirection_norm,one_mul])

lemma bulkY_measurable (N : ℕ) (p : Fin N) : Measurable (Function.uncurry (bulkY N p)) :=
  ((bulkDirection_continuous N p).measurable.comp measurable_snd).inner measurable_fst

lemma bulkAmplitude_update (N : ℕ) (v : ℕ→ℝ) (p j : Fin N) (u : ℝ) :
    bulkAmplitude N (Function.update v (p.val+1) u) j=
      bulkAmplitude N (Function.update v (p.val+1) 0) j+u*bulkCoefficient N p*Pi.single (M := fun _ : Fin N => ℝ) p 1 j := by
  classical
  by_cases hj : j=p
  · subst j; simp [bulkAmplitude,bulkCoefficient]; ring
  · have h : j.val+1≠p.val+1 := fun h => hj (Fin.ext (Nat.add_right_cancel h))
    simp [bulkAmplitude,Function.update_of_ne h,Pi.single_eq_of_ne hj]

lemma bulkFeature_update (N : ℕ) (v : ℕ→ℝ) (p : Fin N) (u : ℝ) (x : NormalizedSpin N) :
    bulkFeature N (Function.update v (p.val+1) u) x=
      bulkFeature N (Function.update v (p.val+1) 0) x+(u*bulkCoefficient N p) • bulkDirection N p x := by
  ext i
  cases i with
  | inl i => simp [bulkFeature,bulkDirection,enrichedFeature]
  | inr j =>
    change bulkAmplitude N (Function.update v (p.val+1) u) j.1*spinTensorFeature N _ x j.2 =
      bulkAmplitude N (Function.update v (p.val+1) 0) j.1*spinTensorFeature N _ x j.2 +
      (u*bulkCoefficient N p)*(Pi.single (M := fun _ : Fin N => ℝ) p 1 j.1*spinTensorFeature N _ x j.2)
    rw [bulkAmplitude_update]
    ring

lemma bulkHamiltonian_update (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin N) (u : ℝ)
    (a : BulkDisorder N M) (x : NormalizedSpin N) :
    bulkHamiltonian N M f (Function.update v (p.val+1) u) a.1 a.2 x =
      bulkHamiltonian N M f (Function.update v (p.val+1) 0) a.1 a.2 x+u*(bulkCoefficient N p*bulkY N p a.2 x) := by
  simp only [bulkHamiltonian]
  rw [bulkFeature_update N v p u x]
  simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial,bulkY]
  ring

lemma bulkCoefficient_pos (n : ℕ) (p : Fin (n+1)) : 0<bulkCoefficient (n+1) p := by
  unfold bulkCoefficient bulkScale
  rw [perturbationWeight_eq]
  positivity

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI

import Mathlib

namespace OAI

/-! Integrable Pdf Mul. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKGaussian

 

theorem integrable_pdf_mul {f : ℝ → ℝ} (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun x => (gaussianPDF_lt_top (x := x)))).1 hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using h

 
theorem hasDerivAt_standardDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hp : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert (((hasDerivAt_id x).fun_pow 2).fun_neg.div_const 2) using 1 <;> try rfl
    norm_num
    ring
  simp only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one]
  convert hp.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  ring

 

theorem integral_mul_eq_integral_deriv {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardDensity x)
    (by convert (integrable_pdf_mul hxf).neg using 1; funext x; simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by convert integrable_pdf_mul hf' using 1; funext x; simp only [Pi.mul_apply]; ring)
    (by convert integrable_pdf_mul hf using 1; funext x; simp only [Pi.mul_apply]; ring)
  simp only [neg_mul, mul_neg, integral_neg] at h
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have heq := neg_injective h
  convert heq using 1 <;> congr 1 <;> funext x <;> ring

 
def standardLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (standardLaw n) := by
  unfold standardLaw
  infer_instance

 

theorem integral_coord_mul_eq {n : ℕ} (k : Fin (n + 1))
    {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hd : ∀ (y : Fin n → ℝ) z,
      HasDerivAt (fun s => f (k.insertNth s y)) (g (k.insertNth z y)) z)
    (hf : Integrable f (standardLaw (n + 1)))
    (hg : Integrable g (standardLaw (n + 1)))
    (hxf : Integrable (fun x => x k * f x) (standardLaw (n + 1))) :
    (∫ x, x k * f x ∂standardLaw (n + 1)) = ∫ x, g x ∂standardLaw (n + 1) := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) k).symm
  have hm : MeasurePreserving e ((gaussianReal 0 1).prod (standardLaw n))
      (standardLaw (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) k).symm
  have hfp := (hm.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hgp := (hm.integrable_comp hg.aestronglyMeasurable).mpr hg
  have hx := (hm.integrable_comp hxf.aestronglyMeasurable).mpr hxf
  rw [← hm.integral_comp' (fun x => x k * f x), ← hm.integral_comp' g]
  change (∫ x, ((fun x => x k * f x) ∘ e) x ∂(gaussianReal 0 1).prod (standardLaw n)) =
    ∫ x, (g ∘ e) x ∂(gaussianReal 0 1).prod (standardLaw n)
  rw [integral_prod_symm _ hx, integral_prod_symm _ hgp]
  apply integral_congr_ae
  filter_upwards [hfp.prod_left_ae, hgp.prod_left_ae, hx.prod_left_ae] with y hfy hgy hxy
  have he (z : ℝ) : e (z, y) = k.insertNth z y := rfl
  simp only [Function.comp_apply, he, Fin.insertNth_apply_same] at hfy hgy hxy ⊢
  exact integral_mul_eq_integral_deriv (hd y) hfy hgy hxy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 
def partition (x : ι → ℝ) : ℝ := ∑ i, Real.exp (x i)

def weight (x : ι → ℝ) (i : ι) : ℝ := Real.exp (x i) / partition x

def logPartition (x : ι → ℝ) : ℝ := Real.log (partition x)

def finiteMax (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

theorem partition_pos (x : ι → ℝ) : 0 < partition x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem weight_pos (x : ι → ℝ) (i : ι) : 0 < weight x i :=
  div_pos (Real.exp_pos _) (partition_pos x)

theorem sum_weight (x : ι → ℝ) : ∑ i, weight x i = 1 := by
  simpa only [weight, ← Finset.sum_div, partition] using div_self (partition_pos x).ne'

theorem weight_le_one (x : ι → ℝ) (i : ι) : weight x i ≤ 1 := by
  rw [weight, div_le_one (partition_pos x)]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

omit [Nonempty ι] in
theorem continuous_partition : Continuous (@partition ι _) := by
  unfold partition
  fun_prop

theorem continuous_weight (i : ι) : Continuous (fun x : ι → ℝ => weight x i) := by
  unfold weight
  exact (Real.continuous_exp.comp (continuous_apply i)).div continuous_partition
    (fun x => (partition_pos x).ne')

theorem continuous_logPartition : Continuous (@logPartition ι _) :=
  continuous_partition.log (fun x => (partition_pos x).ne')

theorem le_finiteMax (x : ι → ℝ) (i : ι) : x i ≤ finiteMax x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem le_logPartition (x : ι → ℝ) (i : ι) : x i ≤ logPartition x := by
  rw [logPartition, Real.le_log_iff_exp_le (partition_pos x)]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem finiteMax_le_logPartition (x : ι → ℝ) : finiteMax x ≤ logPartition x := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => le_logPartition x i)

theorem logPartition_le (x : ι → ℝ) :
    logPartition x ≤ finiteMax x + Real.log (Fintype.card ι) := by
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  calc
    logPartition x ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (finiteMax x)) := by
      apply Real.log_le_log (partition_pos x)
      calc
        partition x ≤ ∑ _ : ι, Real.exp (finiteMax x) :=
          Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (le_finiteMax x i)
        _ = _ := by simp
    _ = _ := by rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]; ring

theorem abs_weight_sum_le (x v : ι → ℝ) {M : ℝ} (hM : ∀ i, |v i| ≤ M) :
    |∑ i, weight x i * v i| ≤ M := by
  calc
    |∑ i, weight x i * v i| ≤ ∑ i, |weight x i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weight x i * |v i| := by
      simp only [abs_mul, abs_of_pos (weight_pos _ _)]
    _ ≤ ∑ i, weight x i * M := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hM i) (weight_pos x i).le
    _ = M := by rw [← Finset.sum_mul, sum_weight, one_mul]

theorem hasDerivAt_logPartition {f : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t) :
    HasDerivAt (fun s => logPartition (f s))
      (∑ i, weight (f t) i * v i) t := by
  have h := (HasDerivAt.fun_sum (fun i _ => (hf i).exp)).log (partition_pos (f t)).ne'
  convert h using 1 <;> try rfl
  simp only [weight, div_mul_eq_mul_div, ← Finset.sum_div, partition]

theorem hasDerivAt_weight {f : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun s => f s i) (v i) t) (i : ι) :
    HasDerivAt (fun s => weight (f s) i)
      (weight (f t) i * (v i - ∑ j, weight (f t) j * v j)) t := by
  have h := (hf i).exp.div (HasDerivAt.fun_sum (fun j _ => (hf j).exp))
    (partition_pos (f t)).ne'
  convert h using 1 <;> try rfl
  simp only [weight, div_mul_eq_mul_div, ← Finset.sum_div, partition]
  field_simp

theorem logPartition_abs_le (x : ι → ℝ) :
    |logPartition x| ≤ (∑ i, |x i|) + Real.log (Fintype.card ι) := by
  have hxi (i : ι) : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hm : finiteMax x ≤ ∑ i, |x i| :=
    Finset.sup'_le Finset.univ_nonempty _ (fun i _ => (le_abs_self _).trans (hxi i))
  have hlog := Real.log_natCast_nonneg (Fintype.card ι)
  have hlo : -(∑ i, |x i|) ≤ logPartition x := by
    let i : ι := Classical.choice inferInstance
    exact (neg_le_of_abs_le (hxi i)).trans (le_logPartition x i)
  exact abs_le.mpr ⟨by linarith, (logPartition_le x).trans (add_le_add hm le_rfl)⟩

theorem integrable_logPartition {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ι → ℝ}
    (hf : ∀ i, Integrable (fun x => f x i) μ) :
    Integrable (fun x => logPartition (f x)) μ := by
  apply ((integrable_finsetSum _ fun i _ => (hf i).abs).add
    (integrable_const (Real.log (Fintype.card ι)))).mono'
  · exact continuous_logPartition.comp_aestronglyMeasurable
      (integrable_pi_iff.mpr hf).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Pi.add_apply] using logPartition_abs_le (f x)

 
def linearField {n : ℕ} (A : ι → Fin n → ℝ) (x : Fin n → ℝ) (i : ι) : ℝ :=
  ∑ k, A i k * x k

omit [Fintype ι] [Nonempty ι] in
theorem continuous_linearField {n : ℕ} (A : ι → Fin n → ℝ) :
    Continuous (linearField A) := by
  unfold linearField
  fun_prop

theorem integrable_coordinate {n : ℕ} (k : Fin n) :
    Integrable (fun x : Fin n → ℝ => x k) (standardLaw n) := by
  apply (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) k).integrable_comp
    (measurable_id.aestronglyMeasurable) |>.mpr
  exact MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)

omit [Fintype ι] [Nonempty ι] in
theorem integrable_linearField {n : ℕ} (A : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun x => linearField A x i) (standardLaw n) :=
  integrable_finsetSum _ fun k _ => (integrable_coordinate k).const_mul (A i k)

theorem integrable_weight {n : ℕ} (A : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun x => weight (linearField A x) i) (standardLaw n) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((continuous_weight i).comp (continuous_linearField A)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)] using
      weight_le_one (linearField A x) i

omit [Fintype ι] [Nonempty ι] in
theorem hasDerivAt_linearField_insert {n : ℕ} (A : ι → Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) (y : Fin n → ℝ) (z : ℝ) (i : ι) :
    HasDerivAt (fun s => linearField A (k.insertNth s y) i) (A i k) z := by
  have he (s : ℝ) : linearField A (k.insertNth s y) i =
      A i k * s + ∑ j : Fin n, A i (k.succAbove j) * y j := by
    rw [linearField, Fin.sum_univ_succAbove _ k]
    simp
  simp_rw [he]
  simpa using ((hasDerivAt_id z).const_mul (A i k)).add_const
    (∑ j : Fin n, A i (k.succAbove j) * y j)

 
theorem integrable_weight_derivative {n : ℕ} (A : ι → Fin n → ℝ)
    (i : ι) (k : Fin n) :
    Integrable (fun x => weight (linearField A x) i *
      (A i k - ∑ j, weight (linearField A x) j * A j k)) (standardLaw n) := by
  apply ((integrable_const (A i k)).sub
    (integrable_finsetSum _ fun j _ => (integrable_weight A j).mul_const (A j k))).bdd_mul
    ((continuous_weight i).comp (continuous_linearField A)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)] using
      weight_le_one (linearField A x) i

theorem integrable_coord_weight {n : ℕ} (A : ι → Fin n → ℝ)
    (i : ι) (k : Fin n) :
    Integrable (fun x => x k * weight (linearField A x) i) (standardLaw n) := by
  apply (integrable_coordinate k).mul_bdd
    ((continuous_weight i).comp (continuous_linearField A)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)] using
      weight_le_one (linearField A x) i

 
theorem integral_coord_weight {n : ℕ} (A : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    (∫ x, x k * weight (linearField A x) i ∂standardLaw n) =
      ∫ x, weight (linearField A x) i *
        (A i k - ∑ j, weight (linearField A x) j * A j k) ∂standardLaw n := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
    apply integral_coord_mul_eq k
      (fun y z => hasDerivAt_weight (fun j => hasDerivAt_linearField_insert A k y z j) i)
      (integrable_weight A i) (integrable_weight_derivative A i k)
      (integrable_coord_weight A i k)

omit [Nonempty ι] in
 
theorem weighted_covariance (w a b : ι → ℝ) (hw : ∑ i, w i = 1) :
    (∑ i, ∑ j, w i * w j * (a i - a j) * (b i - b j)) =
      2 * ((∑ i, w i * a i * b i) - (∑ i, w i * a i) * (∑ j, w j * b j)) := by
  have he (i j : ι) : w i * w j * (a i - a j) * (b i - b j) =
      (w i * a i * b i) * w j - (w i * a i) * (w j * b j) -
        (w i * b i) * (w j * a j) + w i * (w j * a j * b j) := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul, mul_one]
  ring

omit [Fintype ι] [Nonempty ι] in
theorem linearField_combo {n : ℕ} (A B : ι → Fin n → ℝ) (a b : ℝ)
    (x : Fin n → ℝ) (i : ι) :
    linearField (fun i k => a * A i k + b * B i k) x i =
      a * linearField A x i + b * linearField B x i := by
  simp only [linearField, add_mul, Finset.sum_add_distrib, ← mul_assoc, Finset.mul_sum]

def rotateCoeff {n : ℕ} (A B : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  Real.cos t * A i k + Real.sin t * B i k

def velocityCoeff {n : ℕ} (A B : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  -Real.sin t * A i k + Real.cos t * B i k

omit [Fintype ι] [Nonempty ι] in
theorem hasDerivAt_rotatedField {n : ℕ} (A B : ι → Fin n → ℝ)
    (x : Fin n → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => linearField (rotateCoeff A B s) x i)
      (linearField (velocityCoeff A B t) x i) t := by
  change HasDerivAt (fun s => linearField (fun i k => Real.cos s * A i k + Real.sin s * B i k) x i)
    (linearField (fun i k => -Real.sin t * A i k + Real.cos t * B i k) x i) t
  simp_rw [linearField_combo]
  exact ((Real.hasDerivAt_cos t).mul_const (linearField A x i)).add
    ((Real.hasDerivAt_sin t).mul_const (linearField B x i))

theorem continuous_weightedMean {n : ℕ} (A D : ι → Fin n → ℝ) :
    Continuous (fun x => ∑ i, weight (linearField A x) i * linearField D x i) := by
  apply continuous_finsetSum
  intro i _
  exact ((continuous_weight i).comp (continuous_linearField A)).mul
    ((continuous_apply i).comp (continuous_linearField D))

theorem integrable_weightedMean {n : ℕ} (A D : ι → Fin n → ℝ) :
    Integrable (fun x => ∑ i, weight (linearField A x) i * linearField D x i)
      (standardLaw n) := by
  apply integrable_finsetSum
  intro i _
  apply (integrable_linearField D i).bdd_mul
    ((continuous_weight i).comp (continuous_linearField A)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)] using
      weight_le_one (linearField A x) i

theorem rotated_derivative_bound {n : ℕ} (A B : ι → Fin n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    |∑ i, weight (linearField (rotateCoeff A B t) x) i *
      linearField (velocityCoeff A B t) x i| ≤
        ∑ i, (|linearField A x i| + |linearField B x i|) := by
  apply abs_weight_sum_le
  intro i
  calc
    |linearField (velocityCoeff A B t) x i| =
      |-Real.sin t * linearField A x i + Real.cos t * linearField B x i| := by
        exact congrArg abs (linearField_combo A B (-Real.sin t) (Real.cos t) x i)
    _ ≤ |Real.sin t| * |linearField A x i| + |Real.cos t| * |linearField B x i| := by
      simpa only [abs_mul, abs_neg] using abs_add_le
        (-Real.sin t * linearField A x i) (Real.cos t * linearField B x i)
    _ ≤ |linearField A x i| + |linearField B x i| := by
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one t))
        (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one t))
    _ ≤ ∑ j, (|linearField A x j| + |linearField B x j|) :=
      Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (linearField A x j))
        (abs_nonneg (linearField B x j))) (Finset.mem_univ i)

 

theorem hasDerivAt_expected_rotated {n : ℕ} (A B : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, logPartition (linearField (rotateCoeff A B s) x) ∂standardLaw n)
      (∫ x, ∑ i, weight (linearField (rotateCoeff A B t) x) i *
        linearField (velocityCoeff A B t) x i ∂standardLaw n) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun x => ∑ i, (|linearField A x i| + |linearField B x i|))
    (F' := fun s x => ∑ i, weight (linearField (rotateCoeff A B s) x) i *
      linearField (velocityCoeff A B s) x i)
    (Filter.univ_mem) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun s =>
      (continuous_logPartition.comp (continuous_linearField (rotateCoeff A B s))).aestronglyMeasurable
  · exact integrable_logPartition (integrable_linearField (rotateCoeff A B t))
  · exact (continuous_weightedMean (rotateCoeff A B t) (velocityCoeff A B t)).aestronglyMeasurable
  · exact ae_of_all _ fun x s _ => by
      simpa only [Real.norm_eq_abs] using rotated_derivative_bound A B x s
  · exact integrable_finsetSum _ fun i _ =>
      (integrable_linearField A i).abs.add (integrable_linearField B i).abs
  · exact ae_of_all _ fun x s _ =>
      hasDerivAt_logPartition (fun i => hasDerivAt_rotatedField A B x i s)

 
theorem integral_weightedMean_eq {n : ℕ} (A D : ι → Fin n → ℝ) :
    (∫ x, ∑ i, weight (linearField A x) i * linearField D x i ∂standardLaw n) =
      ∫ x, ∑ i, ∑ k, D i k * (weight (linearField A x) i *
        (A i k - ∑ j, weight (linearField A x) j * A j k)) ∂standardLaw n := by
  have hleft (i : ι) (k : Fin n) :
      Integrable (fun x => D i k * (x k * weight (linearField A x) i)) (standardLaw n) :=
    (integrable_coord_weight A i k).const_mul (D i k)
  have hright (i : ι) (k : Fin n) :
      Integrable (fun x => D i k * (weight (linearField A x) i *
        (A i k - ∑ j, weight (linearField A x) j * A j k))) (standardLaw n) :=
    (integrable_weight_derivative A i k).const_mul (D i k)
  calc
    _ = ∫ x, ∑ i, ∑ k, D i k * (x k * weight (linearField A x) i) ∂standardLaw n := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        apply Finset.sum_congr rfl
        intro i _
        rw [linearField, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ i, ∑ k, D i k * (∫ x, x k * weight (linearField A x) i ∂standardLaw n) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hleft i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hleft i k)]
      simp only [integral_const_mul]
    _ = ∑ i, ∑ k, D i k * (∫ x, weight (linearField A x) i *
        (A i k - ∑ j, weight (linearField A x) j * A j k) ∂standardLaw n) := by
      simp_rw [integral_coord_weight]
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hright i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hright i k)]
      simp only [integral_const_mul]

omit [Nonempty ι] in
theorem pairwise_covariance {n : ℕ} (A D : ι → Fin n → ℝ) (w : ι → ℝ)
    (hw : ∑ i, w i = 1) :
    (∑ i, ∑ k, D i k * (w i * (A i k - ∑ j, w j * A j k))) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, w i * w j *
        ∑ k, (D i k - D j k) * (A i k - A j k) := by
  have hk (k : Fin n) :
      (∑ i, D i k * (w i * (A i k - ∑ j, w j * A j k))) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, w i * w j * (D i k - D j k) * (A i k - A j k) := by
    have h := weighted_covariance w (fun i => D i k) (fun i => A i k) hw
    have he : (∑ i, D i k * (w i * (A i k - ∑ j, w j * A j k))) =
        (∑ i, w i * D i k * A i k) - (∑ i, w i * D i k) * (∑ j, w j * A j k) := by
      calc
        _ = ∑ i, (w i * D i k * A i k - (w i * D i k) * (∑ j, w j * A j k)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [he, h]
    ring
  rw [Finset.sum_comm]
  simp_rw [hk, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

theorem integral_weightedMean_eq_pairwise {n : ℕ} (A D : ι → Fin n → ℝ) :
    (∫ x, ∑ i, weight (linearField A x) i * linearField D x i ∂standardLaw n) =
      ∫ x, (1 / 2 : ℝ) * ∑ i, ∑ j,
        weight (linearField A x) i * weight (linearField A x) j *
          ∑ k, (D i k - D j k) * (A i k - A j k) ∂standardLaw n := by
  rw [integral_weightedMean_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun x => pairwise_covariance A D (weight (linearField A x)) (sum_weight _)

omit [Fintype ι] [Nonempty ι] in
theorem rotated_increment_covariance {n : ℕ} (A B : ι → Fin n → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0) (i j : ι) (t : ℝ) :
    (∑ k, (velocityCoeff A B t i k - velocityCoeff A B t j k) *
      (rotateCoeff A B t i k - rotateCoeff A B t j k)) =
      Real.sin t * Real.cos t *
        ((∑ k, (B i k - B j k) ^ 2) - ∑ k, (A i k - A j k) ^ 2) := by
  have hcross : (∑ k, (A i k - A j k) * (B i k - B j k)) = 0 := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, hAB]
    ring
  have he (k : Fin n) :
      (velocityCoeff A B t i k - velocityCoeff A B t j k) *
        (rotateCoeff A B t i k - rotateCoeff A B t j k) =
      Real.sin t * Real.cos t * ((B i k - B j k) ^ 2 - (A i k - A j k) ^ 2) +
        (Real.cos t ^ 2 - Real.sin t ^ 2) * ((A i k - A j k) * (B i k - B j k)) := by
    unfold velocityCoeff rotateCoeff
    ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hcross]
  ring

 

theorem expected_rotated_derivative_nonneg {n : ℕ} (A B : ι → Fin n → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0)
    (hinc : ∀ i j, (∑ k, (A i k - A j k) ^ 2) ≤ ∑ k, (B i k - B j k) ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ ∫ x, ∑ i, weight (linearField (rotateCoeff A B t) x) i *
      linearField (velocityCoeff A B t) x i ∂standardLaw n := by
  rw [integral_weightedMean_eq_pairwise]
  apply integral_nonneg
  intro x
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)
  rw [rotated_increment_covariance A B hAB]
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (ht.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  exact mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hinc i j))

 

theorem expected_logPartition_le {n : ℕ} (A B : ι → Fin n → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0)
    (hinc : ∀ i j, (∑ k, (A i k - A j k) ^ 2) ≤ ∑ k, (B i k - B j k) ^ 2) :
    (∫ x, logPartition (linearField A x) ∂standardLaw n) ≤
      ∫ x, logPartition (linearField B x) ∂standardLaw n := by
  have hc : Continuous (fun t => ∫ x, logPartition (linearField (rotateCoeff A B t) x) ∂standardLaw n) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_expected_rotated A B t).continuousAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (Real.pi / 2))
    hc.continuousOn (fun t _ => (hasDerivAt_expected_rotated A B t).hasDerivWithinAt)
    (fun t ht => expected_rotated_derivative_nonneg A B hAB hinc (interior_subset ht))
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have h := hm (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_rfl, hpi⟩)
    (show Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) from ⟨hpi, le_rfl⟩) hpi
  have h0 : rotateCoeff A B 0 = A := by funext i k; simp [rotateCoeff]
  have h1 : rotateCoeff A B (Real.pi / 2) = B := by funext i k; simp [rotateCoeff]
  simpa only [h0, h1] using h

theorem finiteMax_abs_le (x : ι → ℝ) : |finiteMax x| ≤ ∑ i, |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty) x
  rw [finiteMax, hi]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem continuous_finiteMax : Continuous (@finiteMax ι _ _) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ => continuous_apply i

theorem integrable_finiteMax {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ι → ℝ} (hf : ∀ i, Integrable (fun x => f x i) μ) :
    Integrable (fun x => finiteMax (f x)) μ := by
  apply (integrable_finsetSum _ fun i _ => (hf i).abs).mono'
  · exact continuous_finiteMax.comp_aestronglyMeasurable
      (integrable_pi_iff.mpr hf).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using finiteMax_abs_le (f x)

theorem finiteMax_const_mul (x : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finiteMax (fun i => c * x i) = c * finiteMax x := by
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ fun i _ =>
      mul_le_mul_of_nonneg_left (le_finiteMax x i) hc
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty) x
    change c * Finset.univ.sup' Finset.univ_nonempty x ≤ _
    rw [hi]
    exact le_finiteMax (fun i => c * x i) i

omit [Fintype ι] [Nonempty ι] in
theorem linearField_const_mul {n : ℕ} (A : ι → Fin n → ℝ) (c : ℝ)
    (x : Fin n → ℝ) (i : ι) :
    linearField (fun i k => c * A i k) x i = c * linearField A x i := by
  simp only [linearField, mul_assoc, Finset.mul_sum]

 

theorem expected_finiteMax_le {n : ℕ} (A B : ι → Fin n → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0)
    (hinc : ∀ i j, (∑ k, (A i k - A j k) ^ 2) ≤ ∑ k, (B i k - B j k) ^ 2) :
    (∫ x, finiteMax (linearField A x) ∂standardLaw n) ≤
      ∫ x, finiteMax (linearField B x) ∂standardLaw n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let c : ℝ := (Real.log (Fintype.card ι) + 1) / ε
  have hc : 0 < c := div_pos (by linarith [Real.log_natCast_nonneg (Fintype.card ι)]) hε
  let A' : ι → Fin n → ℝ := fun i k => c * A i k
  let B' : ι → Fin n → ℝ := fun i k => c * B i k
  have hor : ∀ i j, ∑ k, A' i k * B' j k = 0 := by
    intro i j
    calc
      _ = c ^ 2 * ∑ k, A i k * B j k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [A', B']
        ring
      _ = 0 := by rw [hAB, mul_zero]
  have hdist : ∀ i j, (∑ k, (A' i k - A' j k) ^ 2) ≤ ∑ k, (B' i k - B' j k) ^ 2 := by
    intro i j
    have he (C : ι → Fin n → ℝ) :
        (∑ k, (c * C i k - c * C j k) ^ 2) = c ^ 2 * ∑ k, (C i k - C j k) ^ 2 := by
      simp only [← mul_sub, mul_pow, Finset.mul_sum]
    change (∑ k, (c * A i k - c * A j k) ^ 2) ≤ ∑ k, (c * B i k - c * B j k) ^ 2
    rw [he A, he B]
    exact mul_le_mul_of_nonneg_left (hinc i j) (sq_nonneg c)
  have hscaled : c * (∫ x, finiteMax (linearField A x) ∂standardLaw n) ≤
      c * (∫ x, finiteMax (linearField B x) ∂standardLaw n) + Real.log (Fintype.card ι) := by
    calc
      _ = ∫ x, finiteMax (linearField A' x) ∂standardLaw n := by
        simp_rw [show ∀ x, linearField A' x = fun i => c * linearField A x i from
          fun x => funext fun i => linearField_const_mul A c x i,
          finiteMax_const_mul _ hc.le, integral_const_mul]
      _ ≤ ∫ x, logPartition (linearField A' x) ∂standardLaw n :=
        integral_mono (integrable_finiteMax (integrable_linearField A'))
          (integrable_logPartition (integrable_linearField A'))
          (fun x => finiteMax_le_logPartition (linearField A' x))
      _ ≤ ∫ x, logPartition (linearField B' x) ∂standardLaw n :=
        expected_logPartition_le A' B' hor hdist
      _ ≤ ∫ x, finiteMax (linearField B' x) + Real.log (Fintype.card ι) ∂standardLaw n :=
        integral_mono (integrable_logPartition (integrable_linearField B'))
          ((integrable_finiteMax (integrable_linearField B')).add (integrable_const _))
          (fun x => logPartition_le (linearField B' x))
      _ = _ := by
        rw [integral_add (integrable_finiteMax (integrable_linearField B')) (integrable_const _)]
        simp_rw [show ∀ x, linearField B' x = fun i => c * linearField B x i from
          fun x => funext fun i => linearField_const_mul B c x i,
          finiteMax_const_mul _ hc.le, integral_const_mul]
        simp
  have heps : c * ε = Real.log (Fintype.card ι) + 1 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hε.ne'
  nlinarith

 
def gaussianLaw (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (κ : Type*) [Fintype κ] : IsProbabilityMeasure (gaussianLaw κ) := by
  unfold gaussianLaw
  infer_instance

 
def field {κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (x : κ → ℝ) (i : ι) : ℝ :=
  ∑ k, A i k * x k

omit [Fintype ι] [Nonempty ι] in
theorem integrable_field {κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (i : ι) :
    Integrable (fun x => field A x i) (gaussianLaw κ) := by
  apply integrable_finsetSum
  intro k _
  apply Integrable.const_mul
  change Integrable (fun x : κ → ℝ => id (x k)) (Measure.pi fun _ : κ => gaussianReal 0 1)
  apply integrable_comp_eval
  exact MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)

omit [Fintype ι] [Nonempty ι] in
theorem integral_reindex_field {κ : Type*} [Fintype κ] (A : ι → κ → ℝ)
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f (linearField (fun i k => A i ((Fintype.equivFin κ).symm k)) x)
      ∂standardLaw (Fintype.card κ)) = ∫ x, f (field A x) ∂gaussianLaw κ := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let T : (Fin (Fintype.card κ) → ℝ) ≃ᵐ (κ → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hm : MeasurePreserving T (standardLaw (Fintype.card κ)) (gaussianLaw κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have he (x : Fin (Fintype.card κ) → ℝ) :
      field A (T x) = linearField (fun i k => A i (e k)) x := by
    funext i
    show (∑ k, A i k * T x k) = ∑ k, A i (e k) * x k
    rw [← e.sum_comp (fun k => A i k * T x k)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [T, MeasurableEquiv.piCongrLeft_apply_apply]
  have h := hm.integral_comp' (fun x => f (field A x))
  simp_rw [he] at h
  exact h

 
theorem expected_field_max_le_of_orthogonal {κ : Type*} [Fintype κ]
    (A B : ι → κ → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0)
    (hinc : ∀ i j, (∑ k, (A i k - A j k) ^ 2) ≤ ∑ k, (B i k - B j k) ^ 2) :
    (∫ x, finiteMax (field A x) ∂gaussianLaw κ) ≤
      ∫ x, finiteMax (field B x) ∂gaussianLaw κ := by
  rw [← integral_reindex_field A finiteMax, ← integral_reindex_field B finiteMax]
  apply expected_finiteMax_le
  · intro i j
    exact ((Fintype.equivFin κ).symm.sum_comp (fun k => A i k * B j k)).trans (hAB i j)
  · intro i j
    exact ((Fintype.equivFin κ).symm.sum_comp (fun k => (A i k - A j k) ^ 2)).le.trans
      ((hinc i j).trans ((Fintype.equivFin κ).symm.sum_comp (fun k => (B i k - B j k) ^ 2)).symm.le)

omit [Fintype ι] [Nonempty ι] in
 
theorem integral_field_inl {κ κ₂ : Type*} [Fintype κ] [Fintype κ₂] (A : ι → κ → ℝ)
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f (field (fun i => Sum.elim (A i) (fun _ : κ₂ => 0)) x) ∂gaussianLaw (κ ⊕ κ₂)) =
      ∫ x, f (field A x) ∂gaussianLaw κ := by
  let T : ((κ → ℝ) × (κ₂ → ℝ)) ≃ᵐ ((κ ⊕ κ₂) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ κ₂ => ℝ)).symm
  have hm : MeasurePreserving T ((gaussianLaw κ).prod (gaussianLaw κ₂)) (gaussianLaw (κ ⊕ κ₂)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => gaussianReal 0 1)
  rw [← hm.integral_comp' (fun x => f (field (fun i => Sum.elim (A i) (fun _ : κ₂ => 0)) x))]
  have he (x : (κ → ℝ) × (κ₂ → ℝ)) :
      field (fun i => Sum.elim (A i) (fun _ : κ₂ => 0)) (T x) = field A x.1 := by
    funext i
    simp only [field, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero]
    rfl
  simp_rw [he]
  simpa using integral_fun_fst (μ := gaussianLaw κ) (ν := gaussianLaw κ₂)
    (fun x => f (field A x))

omit [Fintype ι] [Nonempty ι] in
theorem integral_field_inr {κ κ₂ : Type*} [Fintype κ] [Fintype κ₂] (B : ι → κ₂ → ℝ)
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f (field (fun i => Sum.elim (fun _ : κ => 0) (B i)) x) ∂gaussianLaw (κ ⊕ κ₂)) =
      ∫ x, f (field B x) ∂gaussianLaw κ₂ := by
  let T : ((κ → ℝ) × (κ₂ → ℝ)) ≃ᵐ ((κ ⊕ κ₂) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ κ₂ => ℝ)).symm
  have hm : MeasurePreserving T ((gaussianLaw κ).prod (gaussianLaw κ₂)) (gaussianLaw (κ ⊕ κ₂)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => gaussianReal 0 1)
  rw [← hm.integral_comp' (fun x => f (field (fun i => Sum.elim (fun _ : κ => 0) (B i)) x))]
  have he (x : (κ → ℝ) × (κ₂ → ℝ)) :
      field (fun i => Sum.elim (fun _ : κ => 0) (B i)) (T x) = field B x.2 := by
    funext i
    simp only [field, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, zero_add]
    rfl
  simp_rw [he]
  simpa using integral_fun_snd (μ := gaussianLaw κ) (ν := gaussianLaw κ₂)
    (fun x => f (field B x))

 

theorem expected_field_max_le {κ κ₂ : Type*} [Fintype κ] [Fintype κ₂]
    (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ)
    (hinc : ∀ i j, (∑ k, (A i k - A j k) ^ 2) ≤ ∑ k, (B i k - B j k) ^ 2) :
    (∫ x, finiteMax (field A x) ∂gaussianLaw κ) ≤
      ∫ x, finiteMax (field B x) ∂gaussianLaw κ₂ := by
  rw [← integral_field_inl (κ₂ := κ₂) A finiteMax,
    ← integral_field_inr (κ := κ) B finiteMax]
  apply expected_field_max_le_of_orthogonal
  · intro i j
    simp [Fintype.sum_sum_type]
  · intro i j
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
      sq, mul_zero, Finset.sum_const_zero, add_zero, zero_add] using hinc i j

end SKGaussian

end

end OAI

import Mathlib
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1
noncomputable def gaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι ↦ standardGaussian)

instance : IsProbabilityMeasure standardGaussian := by unfold standardGaussian; infer_instance
instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (gaussianProduct ι) := by
  unfold gaussianProduct; infer_instance

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma standardGaussian_integrable_id : Integrable (fun x : ℝ ↦ x) standardGaussian := by
  have hh := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (1 : ℝ≥0∞) (by norm_num))
  exact hh.integrable (by norm_num)

lemma gaussian_stein_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hm : AEStronglyMeasurable f' standardGaussian)
    (hC : ∀ x, |f x|≤C) (hD : ∀ x, |f' x|≤D) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hfm : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  have hfi : Integrable f standardGaussian := Integrable.of_bound hfm.aestronglyMeasurable C
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hf'i : Integrable f' standardGaussian := Integrable.of_bound hm D
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hD x)))
  have hxfi : Integrable (fun x ↦ x*f x) standardGaussian :=
    standardGaussian_integrable_id.mul_bdd hfm.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma gaussian_coordinate_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ ↦ z i) (gaussianProduct ι) := by
  exact ((measurePreserving_eval (fun _ : ι ↦ standardGaussian) i).integrable_comp
    standardGaussian_integrable_id.aestronglyMeasurable).mpr standardGaussian_integrable_id

lemma gaussian_pi_stein_bounded {n : ℕ} (i : Fin n) {f f' : (Fin n → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ z, HasDerivAt (fun x ↦ f (Function.update z i x)) (f' z) (z i))
    (hC : ∀ z, |f z| ≤ C) (hD : ∀ z, |f' z| ≤ D) :
    (∫ z, z i*f z ∂gaussianProduct (Fin n)) = ∫ z, f' z ∂gaussianProduct (Fin n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) i
    have he : MeasurePreserving e.symm (standardGaussian.prod (gaussianProduct (Fin n)))
        (gaussianProduct (Fin (n+1))) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ standardGaussian) i).symm
    have hi : Integrable (fun z : Fin (n+1) → ℝ ↦ z i*f z) (gaussianProduct (Fin (n+1))) :=
      (gaussian_coordinate_integrable i).mul_bdd hf.aestronglyMeasurable
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hC z)))
    have hi' : Integrable f' (gaussianProduct (Fin (n+1))) :=
      Integrable.of_bound hf'.aestronglyMeasurable D
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hD z)))
    have hip : Integrable (fun p ↦ e.symm p i * f (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi.aestronglyMeasurable).mpr hi
    have hi'p : Integrable (fun p ↦ f' (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi'.aestronglyMeasurable).mpr hi'
    rw [← he.integral_comp' (fun z ↦ z i*f z), ← he.integral_comp' f',
      integral_prod _ hip, integral_prod _ hi'p,
      integral_integral_swap (f := fun x y ↦ e.symm (x,y) i * f (e.symm (x,y))) hip,
      integral_integral_swap (f := fun x y ↦ f' (e.symm (x,y))) hi'p]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same]
    change (∫ x, x*f (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian) =
      ∫ x, f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian
    have hmeas : Measurable (fun x : ℝ ↦ i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) := by
      exact e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    apply gaussian_stein_bounded (f' := fun x ↦ f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y))
    · intro x
      simpa only [Fin.update_insertNth,Fin.insertNth_apply_same] using hd (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y)
    · exact (hf'.measurable.comp hmeas).aestronglyMeasurable
    · exact fun x ↦ hC _
    · exact fun x ↦ hD _

noncomputable def partition {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def gibbsWeight {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (x i) / partition x

noncomputable def logPartition {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.log (partition x)

lemma partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : 0 < partition x := by
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gibbsWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 ≤ gibbsWeight x i := le_of_lt (div_pos (Real.exp_pos _) (partition_pos x))

lemma sum_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, gibbsWeight x i = 1 := by
  simp only [gibbsWeight,← Finset.sum_div]
  change partition x / partition x = 1
  exact div_self (ne_of_gt (partition_pos x))

lemma gibbsWeight_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    gibbsWeight x i ≤ 1 := by
  calc
    _ ≤ ∑ j, gibbsWeight x j := Finset.single_le_sum (fun j _ ↦ gibbsWeight_nonneg x j) (Finset.mem_univ i)
    _ = 1 := sum_gibbsWeight x

lemma continuous_partition {ι : Type*} [Fintype ι] : Continuous (@partition ι _) := by
  unfold partition
  fun_prop

lemma continuous_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (i : ι) :
    Continuous (fun x : ι → ℝ ↦ gibbsWeight x i) := by
  exact (Real.continuous_exp.comp (continuous_apply i)).div continuous_partition (fun x ↦ ne_of_gt (partition_pos x))

lemma hasDerivAt_partition {ι : Type*} [Fintype ι] {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ partition (x s)) (∑ i, Real.exp (x t i)*v i) t := by
  simpa only [partition,Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (h i).exp))

lemma hasDerivAt_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ logPartition (x s)) (∑ i, gibbsWeight (x t) i*v i) t := by
  convert (hasDerivAt_partition h).log (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight,Finset.sum_div,mul_div_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hasDerivAt_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) (i : ι) :
    HasDerivAt (fun s ↦ gibbsWeight (x s) i)
      (gibbsWeight (x t) i*(v i-∑ j, gibbsWeight (x t) j*v j)) t := by
  convert (h i).exp.div (hasDerivAt_partition h) (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight]
  rw [show (∑ j, Real.exp (x t j)/partition (x t)*v j) =
      (∑ j, Real.exp (x t j)*v j)/partition (x t) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp [ne_of_gt (partition_pos (x t))]

lemma abs_gibbsMean_le {ι : Type*} [Fintype ι] [Nonempty ι] (x v : ι → ℝ) {C : ℝ}
    (hC : ∀ i, |v i| ≤ C) : |∑ i, gibbsWeight x i*v i| ≤ C := by
  calc
    _ ≤ ∑ i, |gibbsWeight x i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, gibbsWeight x i*|v i| := by simp only [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
    _ ≤ ∑ i, gibbsWeight x i*C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hC i) (gibbsWeight_nonneg _ _))
    _ = C := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

noncomputable def linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) : ℝ :=
  ∑ k, c i k*z k

lemma continuous_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) :
    Continuous (linearProcess c) := by
  unfold linearProcess
  fun_prop

lemma hasDerivAt_linearProcess_update {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) (k : κ) :
    HasDerivAt (fun x ↦ linearProcess c (Function.update z k x) i) (c i k) (z k) := by
  have h : ∀ j, HasDerivAt (fun x ↦ c i j * Function.update z k x j)
      (if j=k then c i k else 0) (z k) := by
    intro j
    by_cases hj : j=k
    · subst j
      simpa only [Function.update_self,ite_true,mul_one,id_eq] using (hasDerivAt_id (z k)).const_mul (c i k)
    · simpa only [Function.update_of_ne hj,ite_eq_right hj] using hasDerivAt_const (z k) (c i j*z j)
  simpa only [linearProcess,Finset.sum_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)

lemma continuous_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Continuous (fun z ↦ gibbsWeight (linearProcess c z) i) :=
  (continuous_gibbsWeight i).comp (continuous_linearProcess c)

lemma integrable_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Integrable (fun z ↦ gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply Integrable.of_bound (continuous_linear_gibbsWeight c i).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma coordinate_gibbsWeight_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) (k : κ) :
    Integrable (fun z ↦ z k*gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply (gaussian_coordinate_integrable k).mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma gaussian_coordinate_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n) := by
  apply gaussian_pi_stein_bounded k (C := 1) (D := 2*∑ j, |c j k|)
  · exact continuous_linear_gibbsWeight c i
  · apply Continuous.mul (continuous_linear_gibbsWeight c i)
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun j _ ↦ (continuous_linear_gibbsWeight c j).mul continuous_const)
  · intro z
    simpa only [Function.update_eq_self] using
      hasDerivAt_gibbsWeight (fun j ↦ hasDerivAt_linearProcess_update c z j k) i
  · intro z
    rw [abs_of_nonneg (gibbsWeight_nonneg _ _)]
    exact gibbsWeight_le_one _ _
  · intro z
    have hsum : ∀ j, |c j k| ≤ ∑ l, |c l k| := fun j ↦
      Finset.single_le_sum (f := fun l ↦ |c l k|) (fun l _ ↦ abs_nonneg _) (Finset.mem_univ j)
    calc
      _ = gibbsWeight (linearProcess c z) i * |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| := by
        rw [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
      _ ≤ |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| :=
        mul_le_of_le_one_left (abs_nonneg _) (gibbsWeight_le_one _ _)
      _ ≤ |c i k| + |∑ j, gibbsWeight (linearProcess c z) j*c j k| := abs_sub _ _
      _ ≤ (∑ j, |c j k|) + (∑ j, |c j k|) := add_le_add (hsum i) (abs_gibbsMean_le _ _ hsum)
      _ = _ := by ring

lemma le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    x i ≤ logPartition x := by
  apply (Real.le_log_iff_exp_le (partition_pos x)).mpr
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

lemma logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {C : ℝ}
    (h : ∀ i, x i ≤ C) : logPartition x ≤ Real.log (Fintype.card ι) + C := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    logPartition x ≤ Real.log ((Fintype.card ι : ℝ)*Real.exp C) := by
      apply Real.log_le_log (partition_pos x)
      calc
        partition x ≤ ∑ _ : ι, Real.exp C := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_exp.mpr (h i))
        _ = _ := by simp
    _ = _ := by rw [Real.log_mul (ne_of_gt hc) (Real.exp_ne_zero _),Real.log_exp]

lemma abs_logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |logPartition x| ≤ |Real.log (Fintype.card ι)| + ∑ i, |x i| := by
  have hsum : ∀ i, |x i| ≤ ∑ j, |x j| := fun i ↦
    Finset.single_le_sum (f := fun j ↦ |x j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have hu := logPartition_le x (fun i ↦ (le_abs_self _).trans (hsum i))
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hl := le_logPartition x i
  have hx := neg_abs_le (x i)
  have hxi := hsum i
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Fintype.card ι)),abs_nonneg (Real.log (Fintype.card ι))]

lemma continuous_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@logPartition ι _) :=
  continuous_partition.log (fun x ↦ ne_of_gt (partition_pos x))

lemma linearProcess_integrable {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ linearProcess c z i) (gaussianProduct κ) :=
  integrable_finsetSum _ (fun k _ ↦ (gaussian_coordinate_integrable k).const_mul (c i k))

lemma logPartition_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ logPartition (linearProcess c z)) (gaussianProduct κ) := by
  have hb := (integrable_const (|Real.log (Fintype.card ι)| : ℝ)).add
    (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs))
  apply hb.mono' ((continuous_logPartition.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.add_apply] using abs_logPartition_le (linearProcess c z))

lemma gibbsWeight_mul_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) {f : (κ → ℝ) → ℝ} (hi : Integrable f (gaussianProduct κ)) :
    Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*f z) (gaussianProduct κ) := by
  simpa only [mul_comm] using hi.mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _))

lemma gaussian_linear_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ) (i : ι) :
    (∫ z, gibbsWeight (linearProcess c z) i * linearProcess d z i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k) - ∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
        ∂gaussianProduct (Fin n) := by
  have hid : ∀ k, Integrable (fun z ↦ d i k * (z k*gibbsWeight (linearProcess c z) i))
      (gaussianProduct (Fin n)) := fun k ↦ (coordinate_gibbsWeight_integrable c i k).const_mul _
  have hic : ∀ k, Integrable (fun z ↦ d i k * (gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k))) (gaussianProduct (Fin n)) := by
    intro k
    apply Integrable.const_mul
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum Finset.univ
      (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  calc
    _ = ∫ z, ∑ k, d i k*(z k*gibbsWeight (linearProcess c z) i) ∂gaussianProduct (Fin n) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z ↦ by simp only [linearProcess,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring)
    _ = ∑ k, d i k * (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hid k)]
      simp only [integral_const_mul]
    _ = ∑ k, d i k * (∫ z, gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n)) := by
      simp only [gaussian_coordinate_gibbsWeight]
    _ = ∫ z, ∑ k, d i k * (gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k)) ∂gaussianProduct (Fin n) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hic k)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring

lemma weighted_covariance_pairs {ι : Type*} [Fintype ι] (p : ι → ℝ) (D : ι → ι → ℝ)
    (hp : ∑ i, p i = 1) :
    ∑ i, p i*(D i i-∑ j, p j*D i j) =
    (1/2 : ℝ)*∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i) := by
  have h1 : (∑ i, ∑ j, p i*p j*D i i) = ∑ i, p i*D i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = p i*D i i*∑ j, p j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [hp,mul_one]
  have h2 : (∑ i, ∑ j, p i*p j*D j j) = ∑ j, p j*D j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ i, p i)*(p j*D j j) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hp,one_mul]
  have h3 : (∑ i, ∑ j, p i*p j*D j i) = ∑ i, ∑ j, p i*p j*D i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hl : (∑ i, p i*(D i i-∑ j, p j*D i j)) =
      (∑ i, p i*D i i) - ∑ i, ∑ j, p i*p j*D i j := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  have hr : (∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i)) =
      2*(∑ i, p i*D i i)-2*(∑ i, ∑ j, p i*p j*D i j) := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [h1,h2,h3]
    ring
  rw [hl,hr]
  ring

end SKValueG
end

end OAI

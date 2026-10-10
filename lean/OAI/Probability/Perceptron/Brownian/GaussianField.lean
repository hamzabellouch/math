import Mathlib
import OAI.Probability.Perceptron.Variational.StableLaplaceConstant

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
section Replicas
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma gaussian_replica_integrationByParts {v : S → ℝ} {n : ℕ} {F : (Fin n → S) → ℝ}
    (hv : Measurable v) (hF : Measurable F) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    (∫ t, t * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t
      ∂gaussianReal 0 1) =
    ∫ t, tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n)
        (fun x => replicaPotential v n x * F x) t - n *
      tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t *
      tiltMean μ v v t ∂gaussianReal 0 1 := by
  rw [gaussian_tilt_integrationByParts _ (replicaPotential_measurable hv n) hF
    (mul_nonneg (Nat.cast_nonneg n) hC) hD (replicaPotential_bound hvC n) hFD]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [replica_mean_potential μ hv hC hvC n t]
    ring

end Replicas

section GibbsProducts
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_law_apply {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ v t s = (ENNReal.ofReal (tiltPartition μ v t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * v x) ∂μ) := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply _ (replicaPotential_measurable hv n)
    (mul_nonneg (Nat.cast_nonneg n) hC) (replicaPotential_bound hvC n) t (MeasurableSet.univ_pi hs),
    replica_partition μ hv n,ENNReal.ofReal_pow (tilt_partition_pos μ hv hC hvC t).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential v n x) =
      ∏ i, Real.exp (t * v (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply μ hv hC hvC t (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma tilt_mean_twice {v w F : S → ℝ} (hw : Measurable w)
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ x, |w x| ≤ D) (s t : ℝ) :
    tiltMean (tiltLaw μ w s) v F t = tiltMean μ (fun x => s*w x+t*v x) F 1 := by
  have := tilt_law_probability μ hw hD hwD s
  have hp := (tilt_partition_pos μ hw hD hwD s).ne'
  unfold tiltMean tiltIntegral tiltPartition
  rw [tilt_law_integral μ hw hD hwD s,tilt_law_integral μ hw hD hwD s]
  simp only [tiltMean,tiltIntegral,one_mul,Real.exp_add]
  have he (x : S) : Real.exp (s*w x) * (Real.exp (t*v x)*F x) =
      Real.exp (s*w x) * Real.exp (t*v x) * F x := by ring
  simp_rw [he]
  change ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) * F x ∂μ) / tiltPartition μ w s) /
    ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) ∂μ) / tiltPartition μ w s) = _
  rw [div_div_div_cancel_right₀ hp]

end GibbsProducts

lemma gaussian_pi_coordinate_integrationByParts (n : ℕ) (i : Fin (n+1))
    {F D : (Fin (n+1) → ℝ) → ℝ} (hF : Measurable F) (hD : Measurable D)
    {C B : ℝ} (hFC : ∀ g, |F g| ≤ C) (hDB : ∀ g, |D g| ≤ B)
    (hd : ∀ (g : Fin n → ℝ) (t : ℝ),
      HasDerivAt (fun u => F (i.insertNth u g)) (D (i.insertNth t g)) t) :
    (∫ g, g i * F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, D g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hmF : Measurable (fun p : ℝ × (Fin n → ℝ) => F (i.insertNth p.1 p.2)) :=
    hF.comp e.measurable
  have hmD : Measurable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2)) :=
    hD.comp e.measurable
  have hiF : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * F (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) := by
    apply ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst ν |>.mul_bdd
      hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFC (i.insertNth p.1 p.2)
  have hiD : Integrable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    Integrable.of_bound hmD.aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hDB (i.insertNth p.1 p.2))
  rw [← he.integral_comp e.measurableEmbedding (fun g => g i * F g),
    ← he.integral_comp e.measurableEmbedding D]
  change (∫ p : ℝ × (Fin n → ℝ), ((i.insertNth p.1 p.2 : Fin (n+1) → ℝ) i) *
    F (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν) =
      ∫ p : ℝ × (Fin n → ℝ), D (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν
  simp only [Fin.insertNth_apply_same]
  rw [integral_prod_symm _ hiF,integral_prod_symm _ hiD]
  apply integral_congr_ae
  exact ae_of_all _ fun g => standardGaussian_integrationByParts (hd g)
    (hmD.comp (measurable_id.prodMk measurable_const))
    (fun t => hFC (i.insertNth t g)) (fun t => hDB (i.insertNth t g))

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean {Ω : Type*} [MeasurableSpace Ω]
    {v : Ω → S → ℝ} {F : S → ℝ} (hv : Measurable (Function.uncurry v))
    (hF : Measurable F) : Measurable (fun g => tiltMean μ (v g) F 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hv.exp.mul (hF.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable).div
      hv.exp.stronglyMeasurable.integral_prod_right'.measurable

def gaussianField (n : ℕ) (v : Fin n → S → ℝ) (g : Fin n → ℝ) (x : S) : ℝ :=
  ∑ i, g i * v i x

lemma gaussianField_measurable {n : ℕ} {v : Fin n → S → ℝ}
    (hv : ∀ i, Measurable (v i)) :
    Measurable (fun p : (Fin n → ℝ) × S => gaussianField n v p.1 p.2) := by
  unfold gaussianField
  fun_prop

omit [MeasurableSpace S] in
lemma gaussianField_bound {n : ℕ} {v : Fin n → S → ℝ} {C : ℝ}
    (hvC : ∀ i x, |v i x| ≤ C) (g : Fin n → ℝ) (x : S) :
    |gaussianField n v g x| ≤ (∑ i, |g i|) * C := by
  unfold gaussianField
  calc
    _ ≤ ∑ i, |g i * v i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |g i| * C := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvC i x) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

omit [MeasurableSpace S] in
lemma gaussianField_insertNth {n : ℕ} (i : Fin (n+1)) (v : Fin (n+1) → S → ℝ)
    (g : Fin n → ℝ) (t : ℝ) (x : S) :
    gaussianField (n+1) v (i.insertNth t g) x =
      t*v i x + gaussianField n (fun j => v (i.succAbove j)) g x := by
  classical
  rw [gaussianField,Fin.sum_univ_succAbove _ i]
  simp [gaussianField]

omit [IsProbabilityMeasure μ] in
lemma tilt_mean_mulObservable {v F : S → ℝ} (c t : ℝ) :
    tiltMean μ v (fun x => c*F x) t = c * tiltMean μ v F t := by
  unfold tiltMean tiltIntegral
  simp_rw [show ∀ x, Real.exp (t*v x)*(c*F x) = c*(Real.exp (t*v x)*F x) by intro; ring]
  rw [integral_const_mul]
  ring

lemma gaussian_field_coordinate_ibp {n : ℕ} (i : Fin (n+1))
    {v : Fin (n+1) → S → ℝ} {h F : S → ℝ}
    (hv : ∀ j, Measurable (v j)) (hh : Measurable h) (hF : Measurable F)
    {C A D : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hvC : ∀ j x, |v j x| ≤ C) (hhA : ∀ x, |h x| ≤ A) (hFD : ∀ x, |F x| ≤ D)
    (s : ℝ) :
    (∫ g, g i * tiltMean μ (fun x => h x + s*gaussianField (n+1) v g x) F 1
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      s * ∫ g, tiltMean μ (fun x => h x + s*gaussianField (n+1) v g x) (fun x => v i x * F x) 1 -
        tiltMean μ (fun x => h x + s*gaussianField (n+1) v g x) F 1 *
          tiltMean μ (fun x => h x + s*gaussianField (n+1) v g x) (v i) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let H (g : Fin (n+1) → ℝ) (x : S) := h x + s*gaussianField (n+1) v g x
  have hHm : Measurable (Function.uncurry H) := hh.comp measurable_snd |>.add
    ((gaussianField_measurable hv).const_mul s)
  have hHb (g : Fin (n+1) → ℝ) (x : S) : |H g x| ≤ A + |s| * ((∑ j, |g j|)*C) := by
    dsimp [H]
    exact (abs_add_le _ _).trans (add_le_add (hhA x) (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (gaussianField_bound hvC g x) (abs_nonneg s)))
  have hm (K : S → ℝ) (hK : Measurable K) := measurable_tiltMean μ hHm hK
  have hb (K : S → ℝ) (hK : Measurable K) {B : ℝ} (hB : 0 ≤ B)
      (hKB : ∀ x, |K x| ≤ B) (g : Fin (n+1) → ℝ) : |tiltMean μ (H g) K 1| ≤ B :=
    tilt_mean_bound μ (hHm.comp (measurable_const.prodMk measurable_id)) hK
      (by positivity) hB (hHb g) hKB 1
  have hvF (x : S) : |v i x * F x| ≤ C * D := by
    rw [abs_mul]; exact mul_le_mul (hvC i x) (hFD x) (abs_nonneg _) hC
  rw [← integral_const_mul]
  apply gaussian_pi_coordinate_integrationByParts n i (hm F hF)
    (measurable_const.mul ((hm _ ((hv i).mul hF)).sub ((hm F hF).mul (hm _ (hv i)))))
    (hb F hF hD hFD) (B := |s| *(2*C*D))
  · intro g
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
    exact (abs_sub _ _).trans (by
      have h1 := hb _ ((hv i).mul hF) (mul_nonneg hC hD) hvF g
      have h2 := mul_le_mul (hb F hF hD hFD g) (hb _ (hv i) hC (hvC i) g) (abs_nonneg _) hD
      rw [← abs_mul] at h2
      nlinarith)
  · intro g t
    let w (x : S) := h x + s*gaussianField n (fun j => v (i.succAbove j)) g x
    have hwm : Measurable w := hh.add (((gaussianField_measurable (fun j => hv (i.succAbove j))).comp
      (measurable_const.prodMk measurable_id)).const_mul s)
    have hwb (x : S) : |w x| ≤ A+|s| *((∑ j, |g j|)*C) := by
      exact (abs_add_le _ _).trans (add_le_add (hhA x) (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (gaussianField_bound (fun j => hvC (i.succAbove j)) g x)
          (abs_nonneg s)))
    have := tilt_law_probability μ hwm (by positivity) hwb 1
    have hsc (x : S) : |s*v i x| ≤ |s| *C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvC i x) (abs_nonneg s)
    have he (K : S → ℝ) (u : ℝ) : tiltMean (tiltLaw μ w 1) (fun x => s*v i x) K u =
        tiltMean μ (H (i.insertNth u g)) K 1 := by
      rw [tilt_mean_twice μ hwm (by positivity) hwb]
      congr 2
      funext x
      dsimp [w,H]
      rw [gaussianField_insertNth]
      ring
    have hd := tilt_mean_deriv (tiltLaw μ w 1) ((hv i).const_mul s) hF
      (mul_nonneg (abs_nonneg s) hC) hD hsc hFD t
    rw [show tiltMean (tiltLaw μ w 1) (fun x => s*v i x) F =
      (fun u => tiltMean μ (H (i.insertNth u g)) F 1) from funext (he F)] at hd
    simp_rw [he] at hd
    convert! hd using 1
    rw [show (fun x => s*v i x * F x) = (fun x => s*(v i x*F x)) by funext x; ring,
      tilt_mean_mulObservable,tilt_mean_mulObservable]
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [show v i * F = (fun x => v i x * F x) from rfl]
    ring

end GaussianField

lemma ennreal_rpow_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : (∑ i ∈ s, f i)^a ≤ ∑ i ∈ s, (f i)^a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ha]
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans (add_le_add le_rfl ih)

lemma ennreal_rpow_tsum_le (f : ℕ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' i, f i)^a ≤ ∑' i, (f i)^a := by
  apply le_of_tendsto_of_tendsto
    ((ENNReal.continuous_rpow_const).continuousAt.tendsto.comp
      (ENNReal.summable.hasSum.tendsto_sum_nat (f := f)))
    (ENNReal.summable.hasSum.tendsto_sum_nat (f := fun i => (f i)^a))
  exact Filter.Eventually.of_forall fun n => ennreal_rpow_sum_le _ _ ha ha1

lemma finitePoissonLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) {f : S → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂finitePoissonLaw r ν, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η := by
  rw [finitePoissonLaw,Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_map_iff (finitePointMeasure_measurable n).aemeasurable
    (measurableSet_le ((Measure.measurable_lintegral hf).pow_const a)
      (Measure.measurable_lintegral (hf.pow_const a)))]
  apply ae_of_all
  intro y
  simp only [finitePointMeasure,lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf,lintegral_dirac' _ (hf.pow_const a)]
  exact ennreal_rpow_sum_le _ _ ha ha1

lemma countablePoissonLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ≥0∞} (hf : Measurable f) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂countablePoissonLaw r ν, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η := by
  rw [countablePoissonLaw,ae_map_iff measureSum_measurable.aemeasurable
    (measurableSet_le ((Measure.measurable_lintegral hf).pow_const a)
      (Measure.measurable_lintegral (hf.pow_const a)))]
  have hi (i : ℕ) : ∀ᵐ η ∂Measure.infinitePi (fun j => finitePoissonLaw (r j) (ν j)),
      (∫⁻ x, f x ∂η i)^a ≤ ∫⁻ x, (f x)^a ∂η i :=
    (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (r j) (ν j)) i).quasiMeasurePreserving.ae
      (finitePoissonLaw_rpow_lintegral_le (r i) (ν i) hf ha ha1)
  filter_upwards [ae_all_iff.mpr hi] with η hη
  simp only [lintegral_sum_measure]
  exact (ennreal_rpow_tsum_le _ ha ha1).trans (ENNReal.tsum_le_tsum hη)

lemma poissonRandomMeasureLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η :=
  countablePoissonLaw_rpow_lintegral_le _ _ hf ha ha1

lemma ennreal_rpow_le_one_add {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ≥0∞) :
    u^a ≤ 1+u := by
  by_cases h : u ≤ 1
  · exact (ENNReal.rpow_le_one h ha0).trans (le_add_right le_rfl)
  · have hu : u^a ≤ u := by simpa using ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge h) ha1
    exact hu.trans (le_add_left le_rfl)

lemma poissonRandomMeasureLaw_fractional_moment {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f g : S → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hfin : ∫⁻ x, f x ∂κ ≠ ⊤) (hgin : ∫⁻ x, (g x)^a ∂κ ≠ ⊤) :
    (∫⁻ η, (∫⁻ x, f x+g x ∂η)^a ∂poissonRandomMeasureLaw κ) ≠ ⊤ := by
  have hbound : ∀ᵐ η ∂poissonRandomMeasureLaw κ,
      (∫⁻ x, f x+g x ∂η)^a ≤ 1+(∫⁻ x, f x ∂η)+(∫⁻ x, (g x)^a ∂η) := by
    filter_upwards [poissonRandomMeasureLaw_rpow_lintegral_le κ hg ha ha1] with η hη
    rw [lintegral_add_left hf]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans
      (add_le_add (ennreal_rpow_le_one_add ha.le ha1 _) hη)
  apply ne_top_of_le_ne_top _ (lintegral_mono_ae hbound)
  rw [lintegral_add_left (f := fun η => 1+(∫⁻ x, f x ∂η)) (measurable_const.add (Measure.measurable_lintegral hf)),
    lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const,lintegral_const,measure_univ,one_mul,
    poissonRandomMeasureLaw_campbell κ hf,poissonRandomMeasureLaw_campbell κ (hg.pow_const a)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨by simp,hfin⟩,hgin⟩

lemma stableLogIntensity_of_integrable {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => b * Real.exp (-b*x) * f x)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂stableLogIntensity b) ≠ ⊤ := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hf.ennreal_ofReal]
  have he (x : ℝ) : ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (f x) =
      ENNReal.ofReal (b * Real.exp (-b*x) * f x) :=
    (ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le)).symm
  simp only [Pi.mul_apply]
  simp_rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x =>
    mul_nonneg (mul_nonneg hb (Real.exp_pos _).le) (hf0 x))).mp hi.hasFiniteIntegral).ne

lemma stableLogIntensity_small_moment {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x, (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Iic (a := 1-b) (by linarith) 0).integrable_indicator
    measurableSet_Iic).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Iic 0).indicator Real.exp x =
      b * (Iic 0).indicator (fun y => Real.exp ((1-b)*y)) x := by
    by_cases hx : x ∈ Iic 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Iic (0 : ℝ)).indicator Real.exp) hb0.le (Real.measurable_exp.indicator measurableSet_Iic)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  congr 1
  funext x
  by_cases hx : x ∈ Iic 0 <;> simp [hx]

lemma stableLogIntensity_large_moment {b a : ℝ} (hb : 0 ≤ b) (hab : a < b) :
    (∫⁻ x, (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Ioi (a := a-b) (by linarith) 0).integrable_indicator
    measurableSet_Ioi).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Ioi 0).indicator (fun y => Real.exp (a*y)) x =
      b * (Ioi 0).indicator (fun y => Real.exp ((a-b)*y)) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Ioi (0 : ℝ)).indicator (fun y => Real.exp (a*y))) hb ((measurable_const.mul measurable_id).exp.indicator measurableSet_Ioi)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  congr 1
  funext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

lemma stablePoissonTotal_fractional_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (ha0 : 0 ≤ a) (hab : a < b) :
    Integrable (fun η => (stablePoissonTotal η)^a) (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  rcases ha0.eq_or_lt with h | ha
  · rw [← h]
    simp only [Real.rpow_zero]
    exact integrable_const 1
  have hh := poissonRandomMeasureLaw_fractional_moment (stableLogIntensity b)
    (f := (Iic (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    (g := (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Iic)
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Ioi)
    ha (hab.trans hb1).le (stableLogIntensity_small_moment hb0 hb1)
  have he (x : ℝ) : ((Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x)^a =
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm x a]
    · simp [indicator_of_notMem hx,ha]
  simp_rw [he] at hh
  specialize hh (stableLogIntensity_large_moment hb0.le hab)
  have he' (x : ℝ) : (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x +
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x = ENNReal.ofReal (Real.exp x) := by
    by_cases hx : x ≤ 0 <;> simp [hx,not_lt.mpr,lt_of_not_ge]
  simp_rw [he'] at hh
  apply Integrable.mono' (integrable_toReal_of_lintegral_ne_top
      ((Measure.measurable_lintegral Real.measurable_exp.ennreal_ofReal).pow_const a).aemeasurable hh)
    ((stablePoissonTotal_measurable.pow_const a).aestronglyMeasurable)
  exact ae_of_all _ fun η => by
    simp only [stablePoissonTotal,Real.norm_eq_abs,ENNReal.toReal_rpow]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_integral {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ)
    (F : (Fin n → S) → ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  rw [← tilt_law_pi μ hv hC hvC n t,tilt_law_integral _
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n)]

end SphericalPerceptronFreeEnergy
end

end OAI

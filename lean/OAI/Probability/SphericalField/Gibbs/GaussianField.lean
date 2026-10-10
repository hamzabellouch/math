import Mathlib
import OAI.Probability.SphericalField.Gibbs.Replicas

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI

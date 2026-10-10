import Mathlib
import OAI.Probability.Perceptron.Variational.HeatLogBCF
import OAI.Probability.Perceptron.Variational.VarianceProdMemLp

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

lemma localMax_second_deriv_nonpos {f : ℝ → ℝ} {u : ℝ}
    (hm : IsLocalMax f u) (hc : ContinuousAt f u) : deriv (deriv f) u ≤ 0 := by
  by_contra! h
  have hn := isLocalMin_of_deriv_deriv_pos h hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 u] (fun _ => f u) := by
    filter_upwards [hm,hn] with x hx hy
    exact le_antisymm hx hy
  have hz := he.deriv.deriv_eq
  simp at hz
  linarith

lemma quadratic_contact_second_deriv {A D : ℝ → ℝ} {u a c v : ℝ}
    (hD : ∀ t, HasDerivAt A (D t) t) (hv : HasDerivAt D v u)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-A t) u) : v ≤ 2*c := by
  let f := fun t => A t-c*(t-a)^2
  have hmax : IsLocalMax f u := by
    simpa only [f,neg_sub] using hmin.neg
  have hd (t : ℝ) : HasDerivAt f (D t-2*c*(t-a)) t := by
    convert! (hD t).sub (((hasDerivAt_id t).sub_const a).pow 2 |>.const_mul c) using 1
    simp
    ring
  have hderiv : deriv f = fun t => D t-2*c*(t-a) := funext fun t => (hd t).deriv
  have h2 : HasDerivAt (deriv f) (v-2*c) u := by
    rw [hderiv]
    simpa only [Pi.sub_def,id_eq,one_mul,mul_one] using hv.sub (((hasDerivAt_id u).sub_const a).const_mul (2*c))
  have hh := localMax_second_deriv_nonpos hmax (hd u).continuousAt
  rw [h2.deriv] at hh
  linarith

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def affineLogRoot (H Y : S → ℝ) (t : ℝ) : ℝ :=
  Real.log (tiltPartition μ (fun x => H x+t*Y x) 1)

lemma affineLogRoot_eq {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    affineLogRoot μ H Y t = Real.log (tiltPartition (tiltLaw μ H 1) Y t) +
      Real.log (tiltPartition μ H 1) := by
  have := tilt_law_probability μ hH hA hHA 1
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hy := tilt_partition_pos (tiltLaw μ H 1) hY hB hYB t
  have he : tiltPartition (tiltLaw μ H 1) Y t * tiltPartition μ H 1 =
      tiltPartition μ (fun x => H x+t*Y x) 1 := by
    unfold tiltPartition
    rw [tilt_law_integral μ hH hA hHA 1]
    simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
    rw [div_mul_cancel₀ _ (by simpa only [tiltPartition,one_mul] using hp.ne')]
    simp_rw [Real.exp_add]
  rw [affineLogRoot,← he,Real.log_mul hy.ne' hp.ne']

lemma affineLogRoot_deriv {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    HasDerivAt (affineLogRoot μ H Y) (tiltMean μ (fun x => H x+t*Y x) Y 1) t := by
  have := tilt_law_probability μ hH hA hHA 1
  have hh := (tilt_log_partition_deriv (tiltLaw μ H 1) hY hB hYB t).add_const
    (Real.log (tiltPartition μ H 1))
  simp_rw [tilt_mean_twice μ hH hA hHA,one_mul] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall fun u => affineLogRoot_eq μ hH hY hA hB hHA hYB u)

lemma affineMean_deriv {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    HasDerivAt (fun u => tiltMean μ (fun x => H x+u*Y x) Y 1)
      (tiltMean μ (fun x => H x+t*Y x) (fun x => Y x*Y x) 1 -
        (tiltMean μ (fun x => H x+t*Y x) Y 1)^2) t := by
  have := tilt_law_probability μ hH hA hHA 1
  have hh := tilt_mean_deriv (tiltLaw μ H 1) hY hY hB hB hYB hYB t
  have he : tiltMean (tiltLaw μ H 1) Y Y = (fun u => tiltMean μ (fun x => H x+u*Y x) Y 1) := by
    funext u
    simpa only [one_mul] using tilt_mean_twice μ (v := Y) (F := Y) hH hA hHA 1 u
  rw [he] at hh
  simpa only [tilt_mean_twice μ hH hA hHA,one_mul,pow_two] using hh

lemma tilt_log_partition_bound {H : S → ℝ} (hH : Measurable H)
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) :
    |Real.log (tiltPartition μ H 1)| ≤ A := by
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hi : Integrable (fun x => Real.exp (H x)) μ := by
    simpa only [one_mul,mul_one] using tilt_integrable μ (F := fun _ => 1) hH measurable_const hA (by norm_num : (0:ℝ) ≤ 1) hHA (fun _ => by norm_num) 1
  have hlo : Real.exp (-A) ≤ tiltPartition μ H 1 := by
    calc
      _ = ∫ _ : S, Real.exp (-A) ∂μ := by simp
      _ ≤ _ := by simpa only [tiltPartition,one_mul] using integral_mono (integrable_const _) hi (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).1)
  have hhi : tiltPartition μ H 1 ≤ Real.exp A := by
    calc
      _ ≤ ∫ _ : S, Real.exp A ∂μ := by simpa only [tiltPartition,one_mul] using integral_mono hi (integrable_const _) (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).2)
      _ = _ := by simp
  exact abs_le.mpr ⟨by simpa using Real.log_le_log (Real.exp_pos (-A)) hlo,by simpa using Real.log_le_log hp hhi⟩

omit [MeasurableSpace S] in
lemma affinePotential_bound {H Y : S → ℝ} {A B : ℝ}
    (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) (x : S) :
    |H x+t*Y x| ≤ A+|t| * B := by
  exact (abs_add_le _ _).trans (add_le_add (hHA x) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYB x) (abs_nonneg t)))

lemma affineLogRoot_convex {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) : ConvexOn ℝ Set.univ (affineLogRoot μ H Y) := by
  have := tilt_law_probability μ hH hA hHA 1
  have he := funext fun t => affineLogRoot_eq μ hH hY hA hB hHA hYB t
  rw [he]
  exact (tilt_log_partition_convex (tiltLaw μ H 1) hY hB hYB).add (convexOn_const _ (convex_univ))

end

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]

def thermalVar (H Y : S → ℝ) (t : ℝ) : ℝ :=
  tiltMean μ (fun x => H x+t*Y x) (fun x => Y x*Y x) 1 -
    (tiltMean μ (fun x => H x+t*Y x) Y 1)^2

lemma thermalVar_nonneg {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) : 0 ≤ thermalVar μ H Y t := by
  have := tilt_law_probability μ hH hA hHA 1
  have he := tilt_variance_eq (tiltLaw μ H 1) hY hB hYB t
  have he' : thermalVar μ H Y t = variance Y (tiltLaw (tiltLaw μ H 1) Y t) := by
    simpa only [thermalVar,tilt_mean_twice μ hH hA hHA,one_mul,pow_two] using he
  rw [he']
  exact variance_nonneg Y _

lemma thermalVar_bound {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) : |thermalVar μ H Y t| ≤ 2*B^2 := by
  have h0 := tilt_mean_bound μ (hH.add (hY.const_mul t)) hY
    (add_nonneg hA (mul_nonneg (abs_nonneg _) hB)) hB (affinePotential_bound hHA hYB t) hYB 1
  have h2 := tilt_mean_bound μ (hH.add (hY.const_mul t)) (hY.mul hY)
    (add_nonneg hA (mul_nonneg (abs_nonneg _) hB)) (sq_nonneg B)
    (affinePotential_bound hHA hYB t) (fun x => by
      simp only [Pi.mul_apply]
      rw [abs_mul,pow_two]; exact mul_le_mul (hYB x) (hYB x) (abs_nonneg _) hB) 1
  simp only [Pi.add_def,Pi.mul_def] at h0 h2
  have hs : |(tiltMean μ (fun x => H x+t*Y x) Y 1)^2| ≤ B^2 := by
    rw [abs_sq]
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hB] using h0)
  unfold thermalVar
  exact (abs_sub _ _).trans (by linarith)

lemma measurable_affineLogRoot {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (t : ℝ) :
    Measurable (fun ω => affineLogRoot μ (H ω) (Y ω) t) := by
  simp only [affineLogRoot,tiltPartition,one_mul]
  exact (hH.add (hY.const_mul t)).exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma measurable_affineMean {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (t : ℝ) :
    Measurable (fun ω => tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1) :=
  measurable_tiltMean_param μ (hH.add (hY.const_mul t)) hY

lemma measurable_thermalVar {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (t : ℝ) :
    Measurable (fun ω => thermalVar μ (H ω) (Y ω) t) := by
  exact (measurable_tiltMean_param μ (hH.add (hY.const_mul t)) (hY.mul hY)).sub
    ((measurable_affineMean μ hH hY t).pow_const 2)

omit [IsProbabilityMeasure P] in
lemma annealedAffineLogRoot_deriv {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hAI : Integrable A P) (hBI : Integrable B P) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, affineLogRoot μ (H ω) (Y ω) u ∂P)
      (∫ ω, tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1 ∂P) t := by
  have hHm (ω) : Measurable (H ω) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun ω => affineLogRoot μ (H ω) (Y ω) t) P := by
    apply (hAI.add (hBI.const_mul |t|)).mono' (measurable_affineLogRoot μ hH hY t).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [affineLogRoot,Real.norm_eq_abs,Pi.add_def] using tilt_log_partition_bound μ
        ((hHm ω).add ((hYm ω).const_mul t)) (add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω)))
        (affinePotential_bound (hHA ω) (hYB ω) t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (s := Set.univ) (bound := B) (F' := fun u ω => tiltMean μ (fun x => H ω x+u*Y ω x) (Y ω) 1)
    (by simp) (Eventually.of_forall fun u => (measurable_affineLogRoot μ hH hY u).aestronglyMeasurable)
    hi (measurable_affineMean μ hH hY t).aestronglyMeasurable
    (ae_of_all _ fun ω u _ => by
      simpa only [Real.norm_eq_abs,Pi.add_def] using tilt_mean_bound μ
        ((hHm ω).add ((hYm ω).const_mul u)) (hYm ω)
        (add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))) (hB ω)
        (affinePotential_bound (hHA ω) (hYB ω) u) (hYB ω) 1)
    hBI (ae_of_all _ fun ω u _ => affineLogRoot_deriv μ (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u)).2

omit [IsProbabilityMeasure P] in
lemma annealedAffineMean_deriv {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hBI : Integrable B P) (hB2 : Integrable (fun ω => (B ω)^2) P) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, tiltMean μ (fun x => H ω x+u*Y ω x) (Y ω) 1 ∂P)
      (∫ ω, thermalVar μ (H ω) (Y ω) t ∂P) t := by
  have hHm (ω) : Measurable (H ω) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun ω => tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1) P := by
    apply hBI.mono' (measurable_affineMean μ hH hY t).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs,Pi.add_def] using tilt_mean_bound μ
        ((hHm ω).add ((hYm ω).const_mul t)) (hYm ω)
        (add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))) (hB ω)
        (affinePotential_bound (hHA ω) (hYB ω) t) (hYB ω) 1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (s := Set.univ) (bound := fun ω => 2*(B ω)^2) (F' := fun u ω => thermalVar μ (H ω) (Y ω) u)
    (by simp) (Eventually.of_forall fun u => (measurable_affineMean μ hH hY u).aestronglyMeasurable)
    hi (measurable_thermalVar μ hH hY t).aestronglyMeasurable
    (ae_of_all _ fun ω u _ => by
      simpa only [Real.norm_eq_abs] using thermalVar_bound μ (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u)
    (hB2.const_mul 2) (ae_of_all _ fun ω u _ => affineMean_deriv μ
      (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u)).2

omit [IsProbabilityMeasure P] in

lemma contact_thermal_variance_le {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hAI : Integrable A P) (hBI : Integrable B P) (hB2 : Integrable (fun ω => (B ω)^2) P)
    {u a c : ℝ}
    (hmin : IsLocalMin (fun t => c*(t-a)^2-∫ ω, affineLogRoot μ (H ω) (Y ω) t ∂P) u) :
    (∫ ω, thermalVar μ (H ω) (Y ω) u ∂P) ≤ 2*c := by
  exact quadratic_contact_second_deriv
    (annealedAffineLogRoot_deriv μ P hH hY hA hB hHA hYB hAI hBI)
    (annealedAffineMean_deriv μ P hH hY hA hB hHA hYB hBI hB2 u) hmin

end SphericalPerceptronFreeEnergy

end

end OAI

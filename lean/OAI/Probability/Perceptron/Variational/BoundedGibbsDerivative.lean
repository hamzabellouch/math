import Mathlib
import OAI.Probability.Perceptron.Variational.HeatLogBCF
import OAI.Probability.Perceptron.Variational.VarianceProdMemLp

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma bounded_gibbs_integral_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltIntegral μ (H u) (F u) 1)
      (∫ x, Real.exp (H t x) * (H' t x * F t x + F' t x) ∂μ) t := by
  simp only [tiltIntegral, one_mul]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u x => Real.exp (H u x)*F u x)
    (s := univ) (bound := fun _ => Real.exp A * (B*C+D))
    (F' := fun u x => Real.exp (H u x) * (H' u x * F u x+F' u x))
    (Filter.univ_mem) (Eventually.of_forall fun u =>
      ((hH.comp (measurable_const.prodMk measurable_id)).exp.mul
        (hF.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (by
      simpa only [one_mul, Function.comp_def, Function.uncurry_def, id_eq, Pi.mul_apply] using tilt_integrable μ
        (hH.comp (measurable_const.prodMk measurable_id))
        (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA t) (hFC t) 1)
    (by fun_prop) (ae_of_all _ fun x u _ => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm (Real.exp (H u x)), mul_comm (Real.exp A)]
    apply mul_le_mul _ (Real.exp_le_exp.mpr ((le_abs_self _).trans (hHA u x)))
      (Real.exp_pos _).le (add_nonneg (mul_nonneg hB hC) hD)
    exact (abs_add_le _ _).trans (add_le_add (by
      rw [abs_mul]; exact mul_le_mul (hHB u x) (hFC u x) (abs_nonneg _) hB) (hFD u x))
  · convert! ((hdH u x).exp.mul (hdF u x)) using 1
    ring

lemma bounded_gibbs_mean_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltMean μ (H u) (F u) 1)
      (tiltMean μ (H t) (fun x => H' t x * F t x+F' t x) 1 -
        tiltMean μ (H t) (F t) 1 * tiltMean μ (H t) (H' t) 1) t := by
  have hnum := bounded_gibbs_integral_deriv μ hH hH' hF hF' hA hB hC hD
    hHA hHB hFC hFD hdH hdF t
  have hden := bounded_gibbs_integral_deriv μ hH hH' (F := fun _ _ => 1)
    (F' := fun _ _ => 0) (C := 1) (D := 0) measurable_const measurable_const hA hB (by norm_num)
    (by norm_num) hHA hHB (by simp) (by simp) hdH (by intro t x; exact hasDerivAt_const _ _) t
  simp only [mul_one, add_zero, tiltIntegral, one_mul] at hden
  have hp := (tilt_partition_pos μ (hH.comp (measurable_const.prodMk measurable_id))
    hA (hHA t) 1).ne'
  have hp' : (∫ x, Real.exp (H t x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition, one_mul, Function.comp_def, Function.uncurry_def, id_eq] using hp
  convert! hnum.div hden hp' using 1
  · simp only [tiltMean, tiltPartition, one_mul, Pi.div_def]
  · simp only [tiltMean, tiltIntegral, tiltPartition, one_mul]
    field_simp [hp']

lemma bounded_gaussian_gibbs_coordinate_ibp {n : ℕ} (i : Fin (n+1))
    {H H' F F' : (Fin (n+1) → ℝ) → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * tiltMean μ (H g) (F g) 1 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, tiltMean μ (H g) (fun x => H' g x*F g x+F' g x) 1 -
        tiltMean μ (H g) (F g) 1 * tiltMean μ (H g) (H' g) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hm := measurable_tiltMean_param μ hH hF
  have hmm := measurable_tiltMean_param μ (Y := fun g x => H' g x*F g x+F' g x) hH ((hH'.mul hF).add hF')
  have hm' := measurable_tiltMean_param μ hH hH'
  have hb (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA g) (hFC g) 1
  have hb' (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hH'.comp (measurable_const.prodMk measurable_id)) hA hB (hHA g) (hHB g) 1
  apply gaussian_pi_coordinate_integrationByParts n i hm (hmm.sub (hm.mul hm'))
    (C := C) (B := 2*B*C+D) hb
  · intro g
    have hab (x) : |H' g x*F g x+F' g x| ≤ B*C+D :=
      (abs_add_le _ _).trans (add_le_add (by
        rw [abs_mul]; exact mul_le_mul (hHB g x) (hFC g x) (abs_nonneg _) hB) (hFD g x))
    have hj := tilt_mean_bound μ
      (hH.comp (measurable_const.prodMk measurable_id))
      (((hH'.mul hF).add hF').comp (measurable_const.prodMk measurable_id))
      hA (by positivity) (hHA g) hab 1
    exact (abs_sub _ _).trans (by
      simp only [Pi.mul_apply, abs_mul]
      have hp := mul_le_mul (hb g) (hb' g) (abs_nonneg _) hC
      simp only [Function.comp_def, Function.uncurry_def, id_eq, Pi.add_apply, Pi.mul_apply] at hj hp
      nlinarith)
  · intro g t
    have he : Measurable (fun p : ℝ×S => ((i.insertNth p.1 g : Fin (n+1) → ℝ),p.2)) := by
      fun_prop
    exact bounded_gibbs_mean_deriv μ
      (H := fun t x => H (i.insertNth t g) x)
      (H' := fun t x => H' (i.insertNth t g) x)
      (F := fun t x => F (i.insertNth t g) x)
      (F' := fun t x => F' (i.insertNth t g) x)
      (hH.comp he) (hH'.comp he) (hF.comp he) (hF'.comp he)
      hA hB hC hD (fun u => hHA _) (fun u => hHB _) (fun u => hFC _) (fun u => hFD _)
      (hdH g) (hdF g) t

lemma nonlinear_pattern_coordinate_ibp {n : ℕ} (i : Fin (n+1)) (f : Jet3)
    {v : Fin (n+1) → S → ℝ} {h u : S → ℝ}
    (hv : ∀ j, Measurable (v j)) (hh : Measurable h) (hu : Measurable u)
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ j x, |v j x| ≤ C) (huD : ∀ x, |u x| ≤ D) :
    (∫ a, a i * tiltMean μ (fun x => h x+f.f (gaussianField (n+1) v a x))
      (fun x => f.d1 (gaussianField (n+1) v a x)*u x) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ a, tiltMean μ (fun x => h x+f.f (gaussianField (n+1) v a x))
        (fun x => (f.d1 (gaussianField (n+1) v a x)^2+
          f.d2 (gaussianField (n+1) v a x))*v i x*u x) 1 -
      tiltMean μ (fun x => h x+f.f (gaussianField (n+1) v a x))
        (fun x => f.d1 (gaussianField (n+1) v a x)*u x) 1 *
      tiltMean μ (fun x => h x+f.f (gaussianField (n+1) v a x))
        (fun x => f.d1 (gaussianField (n+1) v a x)*v i x) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let b := gaussianField (n+1) v
  let H := fun a x => h x+f.f (b a x)
  let H' := fun a x => f.d1 (b a x)*v i x
  let F := fun a x => f.d1 (b a x)*u x
  let F' := fun a x => f.d2 (b a x)*v i x*u x
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hHm : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hH'm : Measurable (Function.uncurry H') :=
    (f.d1.continuous.measurable.comp hb).mul ((hv i).comp measurable_snd)
  have hFm : Measurable (Function.uncurry F) :=
    (f.d1.continuous.measurable.comp hb).mul (hu.comp measurable_snd)
  have hF'm : Measurable (Function.uncurry F') :=
    ((f.d2.continuous.measurable.comp hb).mul ((hv i).comp measurable_snd)).mul (hu.comp measurable_snd)
  have hHA (a x) : |H a x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have hHB (a x) : |H' a x| ≤ ‖f.d1‖*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i x)
      (abs_nonneg _) (norm_nonneg _))
  have hFC (a x) : |F a x| ≤ ‖f.d1‖*D := by
    exact (abs_mul _ _).trans_le (mul_le_mul (f.d1.norm_coe_le_norm _) (huD x)
      (abs_nonneg _) (norm_nonneg _))
  have hFD (a x) : |F' a x| ≤ ‖f.d2‖*C*D := by
    dsimp [F']
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i x)
      (abs_nonneg _) (norm_nonneg _)) (huD x) (abs_nonneg _) (by positivity)
  have hdH (a t x) : HasDerivAt (fun s => H (i.insertNth s a) x)
      (H' (i.insertNth t a) x) t := by
    dsimp [H, H', b]
    simp_rw [gaussianField_insertNth]
    convert! ((f.has1 _).comp t (((hasDerivAt_id t).mul_const (v i x)).add_const
      (gaussianField n (fun j => v (i.succAbove j)) a x))).const_add (h x) using 1
    simp only [one_mul, id_eq]
  have hdF (a t x) : HasDerivAt (fun s => F (i.insertNth s a) x)
      (F' (i.insertNth t a) x) t := by
    dsimp [F, F', b]
    simp_rw [gaussianField_insertNth]
    convert! (((f.has2 _).comp t (((hasDerivAt_id t).mul_const (v i x)).add_const
      (gaussianField n (fun j => v (i.succAbove j)) a x))).mul_const (u x)) using 1
    simp only [one_mul, id_eq]
  have he := bounded_gaussian_gibbs_coordinate_ibp μ i hHm hH'm hFm hF'm
    (by positivity) (by positivity) (by positivity) (by positivity) hHA hHB hFC hFD hdH hdF
  convert! he using 1
  · apply integral_congr_ae
    filter_upwards [] with a
    congr 2
    funext x
    dsimp [H', F, F', b]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI

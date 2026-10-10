import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkReplicaDominated
import OAI.Probability.Perceptron.Pressure.SphericalPatternRadial

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def freshRadial (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) : ℝ :=
  inner ℝ (x 0).val b*f.d1 (inner ℝ (x 0).val b)
def freshSecond (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) : ℝ :=
  f.d2 (inner ℝ (x 0).val b)+f.d1 (inner ℝ (x 0).val b)^2
def freshRadialPair (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  spinOverlap (x 0) (x 1)*f.d1 (inner ℝ (x 0).val b)*f.d1 (inner ℝ (x 1).val b)

lemma freshRadial_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshRadial N f)) := by
  have hc : Continuous (Function.uncurry (freshRadial N f)) := by unfold freshRadial Function.uncurry; fun_prop
  exact hc.measurable
lemma freshSecond_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshSecond N f)) := by
  have hc : Continuous (Function.uncurry (freshSecond N f)) := by unfold freshSecond Function.uncurry; fun_prop
  exact hc.measurable
lemma freshRadialPair_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshRadialPair N f)) := by
  have hc : Continuous (Function.uncurry (freshRadialPair N f)) := by unfold freshRadialPair spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshRadial_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) :
    |freshRadial N f b x|≤‖f.d1‖*‖b‖ := by
  unfold freshRadial
  rw [abs_mul,mul_comm]
  exact mul_le_mul (f.d1.norm_coe_le_norm _) (normalizedSpin_inner_bound (x 0) b) (abs_nonneg _) (norm_nonneg _)
lemma freshSecond_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) :
    |freshSecond N f b x|≤‖f.d2‖+‖f.d1‖^2 := by
  apply (abs_add_le _ _).trans
  apply add_le_add (f.d2.norm_coe_le_norm _)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (f.d1.norm_coe_le_norm _) 2
lemma freshRadialPair_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshRadialPair N f b x|≤‖f.d1‖^2 := by
  unfold freshRadialPair
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (spinOverlap_abs_le (x 0) (x 1))
    (f.d1.norm_coe_le_norm (inner ℝ (x 0).val b)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1))
    (f.d1.norm_coe_le_norm (inner ℝ (x 1).val b)) (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma fresh_radial_ibp (n : ℕ) (f : Jet3)
    {h : NormalizedSpin (n+1)→ℝ} (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hb : ∀ x,|h x|≤A) :
    (∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshRadial (n+1) f b) ∂stdGaussian (Spin (n+1))) =
    ∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshSecond (n+1) f b)-
      gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshRadialPair (n+1) f b) ∂stdGaussian (Spin (n+1)) := by
  have hH : Measurable (Function.uncurry (fun b : Spin (n+1) => fun x : NormalizedSpin (n+1) => h x+f.f (inner ℝ x.val b))) :=
    (hh.comp measurable_snd).add (f.f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst))
  have h1 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshRadial_measurable (n+1) f)
  have h2 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshSecond_measurable (n+1) f)
  have h3 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshRadialPair_measurable (n+1) f)
  have h23 : AEStronglyMeasurable (fun b : Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshSecond (n+1) f b)-
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshRadialPair (n+1) f b))
      (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    (h2.sub h3).aestronglyMeasurable
  rw [←map_pi_eq_stdGaussian,integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h1.aestronglyMeasurable,
    integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h23]
  have he := spherical_pattern_radial_ibp (unitSphereLaw (n+1)) f hh hA hb
  unfold freshRadial freshSecond freshRadialPair
  convert he using 1 <;>
    simp only [gaussianField,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]

lemma bulk_radial_last_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+1) f.f v 1 (fun a => freshRadial (n+1) f (bulkSeparateLast (n+1) M a).2) =
      bulkReplicaMean n (M+1) f.f v 1 (fun a => freshSecond (n+1) f (bulkSeparateLast (n+1) M a).2)-
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshRadialPair (n+1) f (bulkSeparateLast (n+1) M a).2) := by
  have hD : Integrable (fun b : Spin (n+1) => ‖f.d1‖*‖b‖) (stdGaussian (Spin (n+1))) :=
    ((((IsGaussian.memLp_id (stdGaussian (Spin (n+1))) 2 (by simp)).norm).integrable (by norm_num))).const_mul _
  rw [bulkReplicaMean_last_integral n M 1 f.f v _ (freshRadial_measurable _ _) hD (fun _ => by positivity) (freshRadial_bound _ _),
    bulkReplicaMean_last_integral n M 1 f.f v _ (freshSecond_measurable _ _) (integrable_const _) (fun _ => by positivity) (freshSecond_bound _ _),
    bulkReplicaMean_last_integral n M 2 f.f v _ (freshRadialPair_measurable _ _) (integrable_const _) (fun _ => by positivity) (freshRadialPair_bound _ _)]
  let P := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 1 (freshSecond (n+1) f p.2)
  let T := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 2 (freshRadialPair (n+1) f p.2)
  have hiP : Integrable P ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 1 f.f v _ (freshSecond_measurable _ _)
      (integrable_const _) (fun _ => by positivity) (freshSecond_bound _ _)
  have hiT : Integrable T ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 2 f.f v _ (freshRadialPair_measurable _ _)
      (integrable_const _) (fun _ => by positivity) (freshRadialPair_bound _ _)
  calc
    _ = ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1), P (a,b)-T (a,b)
        ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => fresh_radial_ibp n f
        (bulkHamiltonian_section_measurable _ _ _ _ a)
        (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ by unfold bulkFeatureBound; positivity)
        (bulkHamiltonian_bound (n+1) M f.f v a)
    _ = _ := by
      have hiPT : Integrable (fun p => P p-T p) ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) := hiP.sub hiT
      rw [←integral_prod _ hiPT,integral_sub hiP hiT,integral_prod _ hiP,integral_prod _ hiT]

lemma bulk_radial_row_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (j : Fin (M+1)) :
    bulkReplicaMean n (M+1) f.f v 1 (fun a => freshRadial (n+1) f (WithLp.toLp 2 (a.1 j))) =
      bulkReplicaMean n (M+1) f.f v 1 (fun a => freshSecond (n+1) f (WithLp.toLp 2 (a.1 j)))-
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshRadialPair (n+1) f (WithLp.toLp 2 (a.1 j))) := by
  rw [bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshRadial_measurable _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshSecond_measurable _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshRadialPair_measurable _ _)]
  exact bulk_radial_last_ibp n M f v

end SphericalPerceptronFreeEnergy
end

end OAI

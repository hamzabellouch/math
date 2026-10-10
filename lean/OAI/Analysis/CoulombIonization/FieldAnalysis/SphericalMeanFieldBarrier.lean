import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BoundedL1PotentialBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.RotationShellBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

def sphereMean (f : Space → ℝ) (p : Space) : ℝ :=
  ∫ g : SpatialRotation, f (rotate g p) ∂rotationMeasure

lemma potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  ((bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.comp
    (continuous_subtype_val.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

lemma rotation_density_kernel_measurable {ρ : Space → ℝ}
    (hm : Measurable ρ) (p : Space) :
    Measurable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖) := by
  have hg : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    continuous_subtype_val.fst'.clm_apply continuous_const
  exact (hm.comp measurable_snd).div (hg.sub continuous_snd).norm.measurable

lemma rotation_density_kernel_normIntegral {ρ : Space → ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (p : Space) (g : SpatialRotation) :
    (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = tfPotential ρ (rotate g p) := by
  change (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = ∫ z : Space, ρ z/‖rotate g p-z‖
  exact integral_congr_ae (ae_of_all _ (fun z => Real.norm_of_nonneg
    (div_nonneg (hn z) (norm_nonneg _))))

lemma rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  refine (integrable_prod_iff (μ := rotationMeasure) (ν := volume)
    (rotation_density_kernel_measurable hm p).aestronglyMeasurable).mpr ⟨?_,?_⟩
  · exact ae_of_all _ (fun g => bounded_L1_potential_integrable hm hi hM hn hb (rotate g p))
  · have he : (fun g : SpatialRotation => ∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) =
        fun g => tfPotential ρ (rotate g p) :=
      funext (rotation_density_kernel_normIntegral hn p)
    rw [he]
    exact potential_rotation_integrable hm hi hM hn hb p

theorem sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  have hs : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
    apply ae_iff.mpr
    have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
      ext a
      simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
    rw [he]
    exact Measure.addHaar_sphere volume (0:Space) ‖p‖
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (rotation_density_kernel_integrable hm hi hM hn hb p)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hs] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

lemma density_shell_integrable {ρ : Space → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {p : Space} (hp : p ≠ 0) :
    Integrable (fun z => ρ z/max ‖p‖ ‖z‖) := by
  apply (hi.div_const ‖p‖).mono' (hm.div (measurable_const.max measurable_norm)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/max ‖p‖ ‖z‖‖ ≤ ρ z/‖p‖
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))]
    exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

theorem sphereMean_field_bracket {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (Z : ℝ) {p : Space} (hp : p ≠ 0) :
    0 ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ∧
    sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ≤
      (∫ z in {z : Space | ‖p‖ < ‖z‖}, ρ z)/‖p‖ := by
  have hp0 := norm_pos_iff.mpr hp
  have hsh := density_shell_integrable hm hi hn hp
  have hrem := (hi.div_const ‖p‖).sub hsh
  have he : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ =
      ∫ z, ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ := by
    have hf : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p =
        Z/‖p‖-sphereMean (tfPotential ρ) p := by
      unfold sphereMean
      simp only [(rotate _).norm_map]
      rw [integral_sub (integrable_const _) (potential_rotation_integrable hm hi hM hn hb p)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [hf,sphereMean_potential hm hi hM hn hb p,
      integral_sub (hi.div_const _) hsh,integral_div]
    ring
  rw [he]
  have hnrem (z : Space) : 0 ≤ ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (hn z) hp0 (le_max_left _ _))
  refine ⟨integral_nonneg hnrem,?_⟩
  let T : Set Space := {z | ‖p‖ < ‖z‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have ht := (hi.indicator hT).div_const ‖p‖
  have hbrem (z : Space) : ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ ≤ T.indicator ρ z/‖p‖ := by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
      exact sub_le_self _ (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))
    · have hzr : ‖z‖ ≤ ‖p‖ := le_of_not_gt hz
      rw [indicator_of_notMem hz,max_eq_left hzr,sub_self,zero_div]
  calc
    _ ≤ ∫ z, T.indicator ρ z/‖p‖ := integral_mono hrem ht hbrem
    _ = _ := by rw [integral_div,integral_indicator hT]

end CoulombAnalysis

end

end OAI

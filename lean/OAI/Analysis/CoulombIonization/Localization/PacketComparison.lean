import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.Variational.InnerPotential

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def packetPotentialConstant : ℝ := 1+9*packetDensityConstant*unitCoulombIntegral

 lemma packetPotentialConstant_one_le : 1 ≤ packetPotentialConstant := by
   unfold packetPotentialConstant
   nlinarith only [mul_nonneg packetDensityConstant_pos.le unitCoulombIntegral_nonneg]

 lemma packet_potential_uniform (y a : Space) {r : ℝ} (hr : 0 < r) :
     tfPotential (packetDensity y r) a ≤ packetPotentialConstant/r := by
   by_cases ha : 2*r ≤ ‖a-y‖
   · change (∫ z, packetDensity y r z/‖a-z‖) ≤ _
     rw [packetDensity_potential y hr (by linarith)]
     exact (div_le_div_of_nonneg_left (by norm_num) hr (by linarith)).trans
       (div_le_div_of_nonneg_right packetPotentialConstant_one_le hr.le)
   · have ha' : ‖a-y‖ < 2*r := lt_of_not_ge ha
     have hk : Integrable (fun z : Space => truncatedCoulomb (3*r) (a-z)) :=
       (integrable_comp_sub_left _ a).mpr (truncatedCoulomb_integrable _)
     calc
       _ ≤ ∫ z : Space, (packetDensityConstant/r^3)*truncatedCoulomb (3*r) (a-z) := by
         apply integral_mono (tfPotential_integrable (packetDensity_integrable y hr)
           (packetDensity_memLp y hr) a) (hk.const_mul _)
         intro z
         change packetDensity y r z / ‖a-z‖ ≤ (packetDensityConstant/r^3)*truncatedCoulomb (3*r) (a-z)
         by_cases hz : packetDensity y r z = 0
         · simp only [hz,zero_div]
           exact mul_nonneg (by positivity [packetDensityConstant_pos]) (truncatedCoulomb_nonneg _ _)
         · have hs := packetDensity_support y hr hz
           have hd : ‖a-z‖ < 3*r := by
             have ht := norm_sub_le a y
             have ht' := norm_sub_le (a-y) (z-y)
             have he : (a-y)-(z-y) = a-z := by abel
             rw [he] at ht'
             linarith only [ht',hs,ha']
           rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd),mul_one_div]
           exact div_le_div_of_nonneg_right (packetDensity_bound y z hr) (norm_nonneg _)
       _ = 9*packetDensityConstant*unitCoulombIntegral/r := by
         rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb_integral (by positivity)]
         field_simp
         ring
       _ ≤ _ := by
         apply div_le_div_of_nonneg_right _ hr.le
         unfold packetPotentialConstant
         linarith

 lemma packet_source_pair_integrable (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     Integrable (fun p : Space × Space => packetDensity y r p.2/‖p.1-p.2‖)
       (mu.prod volume) := by
   have hm : Measurable (fun p : Space × Space => packetDensity y r p.2/‖p.1-p.2‖) :=
     ((packetDensity_continuous y r).measurable.comp measurable_snd).div
       (measurable_fst.sub measurable_snd).norm
   apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
   refine ⟨ae_of_all _ (fun a => tfPotential_integrable (packetDensity_integrable y hr)
     (packetDensity_memLp y hr) a),?_⟩
   have hnorm (a : Space) : (∫ z, ‖packetDensity y r z/‖a-z‖‖) =
       tfPotential (packetDensity y r) a := by
     simp only [Real.norm_of_nonneg (div_nonneg (packetDensity_nonneg y r _) (norm_nonneg _)),tfPotential]
   simp only [hnorm]
   apply (integrable_const (packetPotentialConstant/r)).mono'
     (hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
   apply ae_of_all
   intro a
   change ‖(∫ z, packetDensity y r z/‖a-z‖)‖ ≤ _
   rw [Real.norm_of_nonneg (integral_nonneg (fun z => div_nonneg (packetDensity_nonneg y r z) (norm_nonneg _)))]
   exact packet_potential_uniform y a hr

 lemma packet_source_pairing (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     (∫ z, packetDensity y r z*sourcePotential mu z) =
       ∫ a, tfPotential (packetDensity y r) a ∂mu := by
   have hi := packet_source_pair_integrable mu y hr
   simp only [sourcePotential,← integral_const_mul,tfPotential]
   calc
     (∫ z, ∫ a, packetDensity y r z*‖z-a‖⁻¹ ∂mu) =
         ∫ z, ∫ a, packetDensity y r z/‖a-z‖ ∂mu := by
       simp only [div_eq_mul_inv,norm_sub_rev]
     _ = _ := (integral_integral_swap hi).symm

 lemma packet_source_integrable (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     Integrable (fun z => packetDensity y r z*sourcePotential mu z) := by
   have hi := (packet_source_pair_integrable mu y hr).integral_prod_right
   simpa only [sourcePotential,← integral_const_mul,div_eq_mul_inv,norm_sub_rev] using hi

 lemma packet_outer_potential (y a : Space) {h : ℝ} (hh : 0 < h)
     (hy : ‖y‖ ≤ 2*h) (ha : h < ‖a‖) :
     tfPotential (packetDensity y (h/4)) a ≤ 16*packetPotentialConstant/‖a‖ := by
   have hap : 0 < ‖a‖ := hh.trans ha
   by_cases hfar : 4*h ≤ ‖a‖
   · have hd : ‖a‖/2 ≤ ‖a-y‖ := by
       have ht := norm_le_norm_sub_add a y
       linarith
     change (∫ z, packetDensity y (h/4) z/‖a-z‖) ≤ _
     rw [packetDensity_potential y (by positivity) (by linarith)]
     calc
       _ ≤ 1/(‖a‖/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
       _ = 2/‖a‖ := by ring
       _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [packetPotentialConstant_one_le]) hap.le
   · have hnear : ‖a‖ < 4*h := lt_of_not_ge hfar
     calc
       _ ≤ packetPotentialConstant/(h/4) := packet_potential_uniform y a (by positivity)
       _ ≤ 16*packetPotentialConstant/‖a‖ := by
         apply (div_le_div_iff₀ (by positivity : 0 < h/4) hap).mpr
         have hc := packetPotentialConstant_one_le
         nlinarith only [mul_le_mul_of_nonneg_left hnear.le (zero_le_one.trans hc)]

 theorem packet_outer_source_bound (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 < h) (hs : ∀ᵐ a ∂mu, h < ‖a‖)
     {y : Space} (hy : ‖y‖ ≤ 2*h) :
     (∫ z, packetDensity y (h/4) z*sourcePotential mu z) ≤
       16*packetPotentialConstant*(∫ a, ‖a‖⁻¹ ∂mu) := by
   have hi : Integrable (fun a : Space => ‖a‖⁻¹) mu := by
     apply (integrable_const (h⁻¹)).mono' (by fun_prop)
     filter_upwards [hs] with a ha
     rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
     exact inv_anti₀ hh ha.le
   rw [packet_source_pairing mu y (by positivity),←integral_const_mul]
   apply integral_mono_ae (packet_source_pair_integrable mu y (by positivity)).integral_prod_left
     (hi.const_mul _)
   filter_upwards [hs] with a ha
   simpa only [tfPotential,div_eq_mul_inv] using packet_outer_potential y a hh hy ha

end CoulombAtom

end

end OAI

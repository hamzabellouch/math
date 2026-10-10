import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OuterFieldMaximum
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicMean
import OAI.Analysis.CoulombIonization.Variational.Inner
import OAI.Analysis.CoulombIonization.Localization.PacketComparison

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def innerFieldTestAnnulus (h : ℝ) : Set Space := {z | h ≤ ‖z‖ ∧ ‖z‖ ≤ 3*h}

 lemma innerFieldTestAnnulus_measurable (h : ℝ) : MeasurableSet (innerFieldTestAnnulus h) :=
   (measurableSet_le measurable_const continuous_norm.measurable).inter
     (measurableSet_le continuous_norm.measurable measurable_const)

 lemma innerFieldTestAnnulus_finite (h : ℝ) : volume (innerFieldTestAnnulus h) < ⊤ :=
   (measure_mono (fun z hz => show z ∈ closedBall (0 : Space) (3*h) by
     simpa only [mem_closedBall,dist_zero_right] using hz.2)).trans_lt ((isCompact_closedBall (0 : Space) (3*h)).measure_lt_top)

 lemma positiveCoreField_annular_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
     IntegrableOn (fun z => max (normalizedCoreField Z lam psi z) 0) (innerFieldTestAnnulus h) := by
   let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
     ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
   apply (integrable_const (Z/h)).mono'
     ((normalizedCoreField_measurable hpsi Z lam).max measurable_const).aestronglyMeasurable
   filter_upwards [ae_restrict_mem (innerFieldTestAnnulus_measurable h)] with z hz
   rw [Real.norm_of_nonneg (le_max_right _ _)]
   exact max_le ((normalizedCoreField_le_nuclear psi hZ hlam z).trans
     (div_le_div_of_nonneg_left hZ hh hz.1)) (div_nonneg hZ hh.le)

 lemma packet_on_inner_annulus {h : ℝ} (hh : 0 < h) {y z : Space}
     (hy : ‖y‖ = 2*h) (hz : packetDensity y (h/4) z ≠ 0) :
     z ∈ innerFieldTestAnnulus h := by
   have hd := packetDensity_support y (show 0 < h/4 by positivity) hz
   have h1 := norm_le_norm_sub_add y z
   have h2 := norm_le_norm_sub_add z y
   rw [norm_sub_rev y z] at h1
   constructor <;> linarith only [hd,h1,h2,hy,hh]

 lemma positiveCoreField_packet_le {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h)
     {y : Space} (hy : ‖y‖ = 2*h) :
     Integrable (fun z => packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0) ∧
     (∫ z, packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0) ≤
       packetDensityConstant/(h/4)^3*
         (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0) := by
   let A := innerFieldTestAnnulus h
   let F := fun z => max (normalizedCoreField Z lam psi z) 0
   have hi := (positiveCoreField_annular_integrable hpsi hZ hlam hh).integrable_indicator
     (innerFieldTestAnnulus_measurable h)
   have hC : 0 ≤ packetDensityConstant/(h/4)^3 := by positivity [packetDensityConstant_pos]
   have hb (z : Space) : packetDensity y (h/4) z*F z ≤
       packetDensityConstant/(h/4)^3*A.indicator F z := by
     by_cases hz : packetDensity y (h/4) z = 0
     · rw [hz,zero_mul]
       exact mul_nonneg hC (indicator_nonneg (fun z _ => le_max_right _ _) z)
     · rw [indicator_of_mem (packet_on_inner_annulus hh hy hz)]
       exact mul_le_mul_of_nonneg_right (packetDensity_bound y z (by positivity)) (le_max_right _ _)
   have hp : Integrable (fun z => packetDensity y (h/4) z*F z) := by
     apply (hi.const_mul (packetDensityConstant/(h/4)^3)).mono'
       (((packetDensity_continuous y _).measurable.mul
         ((normalizedCoreField_measurable hpsi Z lam).max measurable_const)).aestronglyMeasurable)
     exact ae_of_all _ (fun z => by
       change ‖packetDensity y (h/4) z*F z‖ ≤ _
       rw [Real.norm_of_nonneg (mul_nonneg (packetDensity_nonneg _ _ _) (le_max_right _ _))]
       exact hb z)
   refine ⟨hp,?_⟩
   calc
     _ ≤ ∫ z, packetDensityConstant/(h/4)^3*A.indicator F z := integral_mono hp (hi.const_mul _) hb
     _ = _ := by rw [integral_const_mul,integral_indicator (innerFieldTestAnnulus_measurable h)]

 def actualInnerBoundaryCap {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) : ℝ :=
   packetDensityConstant/(h/4)^3*
     (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0)+lam+
       16*packetPotentialConstant*(∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖})

 lemma actualInnerBoundaryCap_nonneg {N : ℕ} (psi : FormVector N) (Z : ℝ) {lam h : ℝ}
     (hlam : 0 ≤ lam) (hh : 0 < h) : 0 ≤ actualInnerBoundaryCap psi Z lam h := by
   unfold actualInnerBoundaryCap
   have hp := packetDensityConstant_pos
   have hc := packetPotentialConstant_one_le
   positivity

 theorem actual_inner_boundary_cap {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) {Z lam h : ℝ}
     (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h)
     {y : Space} (hy : ‖y‖ = 2*h) :
     sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h := by
   let mu := actualInnerSource psi h
   let nu := (actualParticleSource psi).restrict {a | h < ‖a‖}
   let : IsFiniteMeasure (actualParticleSource psi) := actualParticleSource_finite hpsi
   let : IsFiniteMeasure mu := actualInnerSource_finite hpsi h
   have hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h := actualInnerSource_support psi h
   have hnu : ∀ᵐ a ∂nu, h < ‖a‖ :=
     ae_restrict_mem (measurableSet_lt measurable_const continuous_norm.measurable)
   have hball : closedBall y (h/2) ⊆ {z | h < ‖z‖} := by
     intro z hz
     have hd : ‖z-y‖ ≤ h/2 := mem_closedBall.mp hz
     have ht := norm_le_norm_sub_add y z
     rw [norm_sub_rev y z] at ht
     change h < ‖z‖
     linarith only [hy,ht,hd,hh]
   have hu := (sourceField_continuousOn Z mu hh.le hs).mono hball
   have hmean : (∫ z, packetDensity y (h/4) z*sourceField Z mu z) = sourceField Z mu y :=
     weak_harmonic_packet_mean_local hu (by positivity) (by linarith)
       (fun g hg hcg hsg => sourceField_weak_harmonic Z mu hh.le hs hg hcg
         (hsg.trans (ball_subset_closedBall.trans hball)))
   have hleft : Integrable (fun z => packetDensity y (h/4) z*sourceField Z mu z) := by
     apply Integrable.congr (continuousOn_mul_integrable_support (isCompact_closedBall y (h/2)) hu
       (packetDensity_continuous y (h/4)) (fun z hz => ?_))
     · exact ae_of_all _ (fun z => mul_comm _ _)
     · rw [mem_closedBall]
       have hd := packetDensity_support y (show 0 < h/4 by positivity) hz
       rw [dist_eq_norm]
       linarith
   obtain ⟨hpos,hposB⟩ := positiveCoreField_packet_le hpsi hZ hlam hh hy
   have hout := packet_source_integrable nu y (show 0 < h/4 by positivity)
   have houtB := packet_outer_source_bound nu hh hnu hy.le
   have hconst := (packetDensity_integrable y (show 0 < h/4 by positivity)).mul_const lam
   have hb (z : Space) : packetDensity y (h/4) z*sourceField Z mu z ≤
       packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0+
         packetDensity y (h/4) z*lam+packetDensity y (h/4) z*sourcePotential nu z := by
     have he := sourceField_inner_eq hpsi hm Z lam h z
     change sourceField Z mu z = normalizedCoreField Z lam psi z+lam+sourcePotential nu z at he
     rw [he,mul_add,mul_add]
     have hh := mul_le_mul_of_nonneg_left
       (le_max_left (normalizedCoreField Z lam psi z) 0) (packetDensity_nonneg y (h/4) z)
     linarith only [hh]
   have hb' := integral_mono hleft ((hpos.add hconst).add hout) hb
   simp only [Pi.add_apply] at hb'
   have hab := integral_add (hpos.add hconst) hout
   have hac := integral_add hpos hconst
   simp only [Pi.add_apply] at hab hac
   rw [hmean,hab,hac,integral_mul_const,
     packetDensity_mass y (show 0 < h/4 by positivity),one_mul] at hb'
   unfold actualInnerBoundaryCap
   change sourceField Z mu y ≤ _
   linarith only [hb',hposB,houtB]

 theorem actual_inner_exterior_cap {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) {Z lam h : ℝ}
     (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) {y : Space} (hy : 2*h ≤ ‖y‖) :
     sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h*(2*h)/‖y‖ := by
   let : IsFiniteMeasure (actualInnerSource psi h) := actualInnerSource_finite hpsi h
   exact sourceField_exterior_comparison Z _ hh.le (by linarith)
     (actualInnerBoundaryCap_nonneg psi Z hlam hh) (actualInnerSource_support psi h)
     (fun z hz => actual_inner_boundary_cap hpsi hm hZ hlam hh hz) hy

end CoulombAtom

end

end OAI

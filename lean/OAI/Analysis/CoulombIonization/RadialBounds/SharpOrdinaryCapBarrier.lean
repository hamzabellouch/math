import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.SphericalMeanFieldBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ExpectedRadialCapBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpOrdinaryCap_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] corePriceExcess

lemma ordinaryDensity_raw_potential {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) :
    tfPotential (ordinaryDensity ψ) y = ∫ x, rawPotential y x ∂formRawLaw ψ := by
  have hkernel : Measurable (fun z : Space => (1:ℝ)/‖y-z‖) := by fun_prop
  have hi (i : Fin N) : Integrable (fun x : Configuration N => (1:ℝ)/‖y-x i‖)
      (formRawLaw ψ) := by
    apply (rawPotential_form_integrable hψ y).mono'
      (hkernel.comp (measurable_pi_apply i)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖(1:ℝ)/‖y-x i‖‖ ≤ rawPotential y x
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [rawPotential,norm_sub_rev (x _) y]
    change (1:ℝ)/‖y-x i‖ ≤ ∑ j, (1:ℝ)/‖y-x j‖
    exact Finset.single_le_sum (f := fun j : Fin N => (1:ℝ)/‖y-x j‖)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hh := ordinaryDensity_pairing hψ hkernel hi
  simpa only [tfPotential,mul_one_div,rawPotential,norm_sub_rev y] using hh

theorem sharp_unconditional_field_cap {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    Z/‖y‖-lam-tfPotential (ordinaryDensity ψ) y ≤
      tfPatchCapConstant/(localCellRadius y)^4+
      sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
        (max (corePriceExcess Z lam ψ) 0) q := by
  obtain ⟨t,ht,ht0,_,hpot⟩ := sharp_joint_selected_patch hψ hy ha1 hb hba hZ hlam hq hqr hcollar
  have ha := localCellRadius_pos hy
  have hnorm : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hraw := radial_center_field_quantitative hψ.sobolevFermion y ht0 hb
    (by linarith [ht.1]) hnorm hZ hlam canonicalRealPacket_smooth canonicalRealPacket_compact
    canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support hq
    (by linarith [ht.1] : q ≤ 3*(t-4*b)/4)
  change |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
    expectedRadialPatchCenter ψ y ht0 hb Z lam| ≤ radialPotentialError ψ y ht0 hb Z lam q at hraw
  rw [hm,mul_one,←ordinaryDensity_raw_potential hψ.sobolevFermion.sobolevVector y] at hraw
  have hcap := expectedRadialPatchCenter_le hψ.sobolevFermion.sobolevVector y ht0 hb
    (by linarith [ht.1]) hnorm Z lam
  rw [hm,mul_one] at hcap
  have hpow : (localCellRadius y)^4 ≤ (t-4*b)^4 :=
    pow_le_pow_left₀ ha.le (by linarith [ht.1]) 4
  have hd := div_le_div_of_nonneg_left tfPatchCapConstant_pos.le
    (by positivity : 0 < (localCellRadius y)^4) hpow
  linarith [(le_abs_self _).trans (hraw.trans hpot),hcap.trans hd]

end CoulombAtom

end Work_SharpOrdinaryCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma ae_off_norm_sphere (p : Space) : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
  apply ae_iff.mpr
  have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
    ext a
    simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume (0:Space) ‖p‖

lemma rotation_kernel_integrable_off_sphere (p z : Space) (hp : p ≠ 0)
    (hz : ‖z‖ ≠ ‖p‖) :
    Integrable (fun g : SpatialRotation => (1:ℝ)/‖rotate g p-z‖) rotationMeasure := by
  by_contra hn
  have he := rotation_kernel_shell p z hz
  rw [integral_undef hn] at he
  have hm : 0 < max ‖p‖ ‖z‖ := (norm_pos_iff.mpr hp).trans_le (le_max_left _ _)
  exact (ne_of_gt (one_div_pos.mpr hm)) he.symm

lemma L1_rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  have hme : AEStronglyMeasurable
      (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) :=
    ((rotation_density_kernel_measurable hm p).comp measurable_swap).aestronglyMeasurable
  have hh : Integrable (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) := by
    apply (integrable_prod_iff hme).mpr
    constructor
    · filter_upwards [ae_off_norm_sphere p] with z hz
      simpa only [mul_one_div] using (rotation_kernel_integrable_off_sphere p z hp hz).const_mul (ρ z)
    · apply (density_shell_integrable hm hi hn hp).congr
      filter_upwards [ae_off_norm_sphere p] with z hz
      change ρ z/max ‖p‖ ‖z‖ = ∫ g : SpatialRotation, ‖ρ z/‖rotate g p-z‖‖ ∂rotationMeasure
      simp_rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
      simp_rw [show ∀ g : SpatialRotation, ρ z/‖rotate g p-z‖ =
        ρ z*((1:ℝ)/‖rotate g p-z‖) by intro g; ring]
      rw [integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]
  exact hh.swap

lemma L1_potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  (L1_rotation_density_kernel_integrable hm hi hn hp).integral_prod_left

theorem L1_sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (L1_rotation_density_kernel_integrable hm hi hn hp)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_off_norm_sphere p] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

lemma L1_residualCharge_le_sphereMean {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    (Z : ℝ) {p : Space} (hp : p ≠ 0) :
    (Z-∫ z, ρ z)/‖p‖ ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p := by
  have hsh := density_shell_integrable hm hi hn hp
  have hf : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p =
      Z/‖p‖-sphereMean (tfPotential ρ) p := by
    unfold sphereMean
    simp only [(rotate _).norm_map]
    rw [integral_sub (integrable_const _) (L1_potential_rotation_integrable hm hi hn hp)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [hf,L1_sphereMean_potential hm hi hn hp,sub_div]
  apply sub_le_sub_left
  rw [←integral_div]
  apply integral_mono hsh (hi.div_const ‖p‖)
  intro z
  exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

theorem L1_residualCharge_of_field_cap {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    (Z : ℝ) {p : Space} (hp : p ≠ 0) {B : ℝ}
    (hcap : ∀ g : SpatialRotation, Z/‖rotate g p‖-tfPotential ρ (rotate g p) ≤ B) :
    Z-∫ z, ρ z ≤ ‖p‖*B := by
  have hh := L1_residualCharge_le_sphereMean hm hi hn Z hp
  have hb : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p ≤ B := by
    have hin : Integrable (fun g : SpatialRotation => Z/‖rotate g p‖-tfPotential ρ (rotate g p)) rotationMeasure := by
      simp only [(rotate _).norm_map]
      exact (integrable_const _).sub (L1_potential_rotation_integrable hm hi hn hp)
    have hv := integral_mono hin (integrable_const B) hcap
    simpa only [sphereMean,integral_const,probReal_univ,smul_eq_mul,one_mul] using hv
  have h := (div_le_iff₀ (norm_pos_iff.mpr hp)).mp (hh.trans hb)
  simpa only [mul_comm] using h

end CoulombAnalysis

end

end OAI

import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PosteriorAnnularQueryBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Set Metric
open scoped NNReal ContDiff
open CoulombAtom
attribute [local irreducible] masterWidth masterKernel

lemma masterWidth_relative_upper_half {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) {y : Space}
    (hy : r₀ ≤ 2*‖y‖) : masterWidth c₁ r₀ s y ≤ 2*c₁*‖y‖ := by
  have hd : masterBaseDistance r₀ y ≤ 2*‖y‖ :=
    max_le (by linarith [norm_nonneg y]) hy
  have hp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  calc
    _ ≤ c₁*masterBaseDistance r₀ y*s^masterExponent := masterWidth_upper hc hr₀ hs y
    _ ≤ c₁*masterBaseDistance r₀ y*1 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hc (le_max_of_le_left (norm_nonneg y)))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd hc]

lemma masterKernel_ne_zero_expanded_annular {g : Space → ℝ}
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ r₀ s r : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hs1 : s ≤ 1) (hrr : r₀ ≤ 2*r) {x y : Space} (hy : r ≤ ‖y‖)
    (hyB : ‖y‖ ≤ B*r) (hxy : masterKernel c₁ r₀ s g x y ≠ 0) :
    r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r := by
  have hr : 0 < r := by linarith
  rw [masterKernel_eq_widthKernel hc hr₀ hs g] at hxy
  have hm := widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
    (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y hxy
  simp only [mem_closedBall,dist_eq_norm] at hm
  have ht := masterWidth_relative_upper_half hc.le hr₀ hs hs1 (by linarith : r₀ ≤ 2*‖y‖)
  have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
  have hd : ‖x-y‖ ≤ ‖y‖/2 := by nlinarith [norm_nonneg y]
  have hl := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hl
  have hu := norm_sub_norm_le x y
  constructor
  · nlinarith only [hl,hd,hy]
  · calc
      ‖x‖ ≤ (3/2:ℝ)*‖y‖ := by linarith only [hu,hd]
      _ ≤ (3/2:ℝ)*(B*r) := mul_le_mul_of_nonneg_left hyB (by norm_num)
      _ ≤ 2*(B*r) := mul_le_mul_of_nonneg_right (by norm_num)
        (mul_nonneg (zero_le_one.trans hB) hr.le)
      _ = 2*B*r := by ring

 theorem exists_master_expanded_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ s r : ℝ}, 0 < r₀ → 0 < s → s ≤ 1 →
      r₀ ≤ 2*r → r ≤ s → ∀ x y z : Space,
      r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r then 1 else 0) := by
  have hcomp : HasCompactSupport (fun q => (g q)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      (masterProfile_support hgs)
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  refine ⟨(H:ℝ)*16*c₁⁻¹^4,by positivity,?_⟩
  intro r₀ s r hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2
  have hr : 0 < r := by linarith
  have hzero : ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ = 0 →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        ((H:ℝ)*16*c₁⁻¹^4)*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r then 1 else 0) := by
    intro he
    rw [he]
    split_ifs <;> positivity
  by_cases ha : masterKernel c₁ r₀ s g x y = 0 ∧ masterKernel c₁ r₀ s g x z = 0
  · exact hzero (by rw [ha.1,ha.2,sub_self,norm_zero])
  have hex : masterKernel c₁ r₀ s g x y ≠ 0 ∨ masterKernel c₁ r₀ s g x z ≠ 0 := by tauto
  have hax : r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*B*r := hex.elim
    (fun h => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hy hy2 h)
    (fun h => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hz hz2 h)
  rw [ite_eq_left hax,mul_one]
  have hlow : c₁*r^(1+masterExponent)/2 ≤ masterWidth c₁ r₀ s x := by
    have haux (q : Space) (hq : r ≤ ‖q‖) (hxq : masterKernel c₁ r₀ s g x q ≠ 0) :
        c₁*r^(1+masterExponent)/2 ≤ masterWidth c₁ r₀ s x := by
      rw [masterKernel_eq_widthKernel hc hr₀ hs g] at hxq
      exact (div_le_div_of_nonneg_right (masterWidth_radius_lower hc.le hr hrs hq) (by norm_num)).trans
        (widthKernel_ne_zero_width_lower (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
          (masterWidth_pos hc hr₀ hs) (masterProfile_support hgs) hxq)
    exact hex.elim (haux y hy) (haux z hz)
  have hinv := pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr₀ hs x).le)
    (inv_anti₀ (by positivity : 0 < c₁*r^(1+masterExponent)/2) hlow) 4
  rw [inverse_fourth_radius_scale hc hr] at hinv
  rw [masterKernel_eq_widthKernel hc hr₀ hs g]
  exact (widthKernel_query_difference (masterWidth_pos hc hr₀ hs) hH x y z).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv H.coe_nonneg)
      (norm_nonneg _)).trans_eq (by ring))

end
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff
open CoulombAtom CoulombObservation
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma posterior_density_le_raw_annular_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ}
    (hg : Continuous g) (y : Space) {a b A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, masterKernel c₁ r₀ s g x y ≤ A)
    (hsupport : ∀ x, masterKernel c₁ r₀ s g x y ≠ 0 → a ≤ ‖x‖ ∧ ‖x‖ ≤ b)
    (d : OriginalDatum N K ell j) :
    jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
      A * ∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j d := by
  let f : Configuration N → ℝ := fun x => ∑ i, masterKernel c₁ r₀ s g (x i) y
  have hm : Measurable f := Finset.measurable_sum _ (fun i _ =>
    ((masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun x : Configuration N => (x i,y))
      ((measurable_pi_apply i).prodMk measurable_const)))
  have hn (x) : 0 ≤ f x := Finset.sum_nonneg fun i _ => masterKernel_nonneg _ _ _ _ _ _
  have hb (x) : f x ≤ A*rawAnnularCount a b x := by
    rw [rawAnnularCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simpa only [mul_one] using hbound (x i)
    · have hz : masterKernel c₁ r₀ s g (x i) y = 0 := by
        by_contra hh
        exact h (hsupport (x i) hh)
      simp only [hz,mul_zero,le_refl]
  have hfb (x) : ‖f x‖ ≤ A*N := by
    rw [Real.norm_of_nonneg (hn x)]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (rawAnnularCount_le a b x) hA)
  have hci : Integrable (rawAnnularCount a b) (originalRawKernel μ ell j d) := by
    apply Integrable.of_bound (rawAnnularCount_measurable a b).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b x)]; exact rawAnnularCount_le a b x)
  unfold jointMasterPosterior
  calc
    _ ≤ ∫ x, A*rawAnnularCount a b x ∂originalRawKernel μ ell j d :=
      integral_mono (Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hfb))
        (hci.const_mul _) hb
    _ = _ := integral_const_mul _ _

theorem exists_posterior_expanded_annular_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ 2*r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y : Space), r ≤ ‖y‖ → ‖y‖ ≤ B*r →
      jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
        D*r^(-3-3*masterExponent) *
          ∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨A,hAn,hA⟩ := masterKernel_amplitude hg hgs
  refine ⟨A*c₁⁻¹^3,by positivity,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hrr hrs d y hy hyB
  have hr : 0 < r := by linarith
  let D := A*c₁⁻¹^3*r^(-3-3*masterExponent)
  have hDn : 0 ≤ D := by dsimp only [D]; positivity
  have hb (x) : masterKernel c₁ r₀ s g x y ≤ D :=
    (hA hc hcL hr₀ hs hs1 x y).trans (by
      simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_left
        (masterWidth_inverse_cube_radius (r₀ := r₀) hc hr hrs hy) hAn)
  exact posterior_density_le_raw_annular_count μ ell j hc hr₀ hs hg y hDn hb
    (fun x hx => masterKernel_ne_zero_expanded_annular hgs hB hc hcL hr₀ hs hs1 hrr hy hyB hx) d

 theorem exists_posterior_expanded_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y z : Space),
      r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
      ‖jointMasterPosterior μ ell j c₁ r₀ s g d y-
        jointMasterPosterior μ ell j c₁ r₀ s g d z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          ∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨C,hC,hbound⟩ := exists_master_expanded_annular_query_constant hg hgs hB hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hr₀s hrr hrs d y z hy hy2 hz hz2
  have hcg : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      ((subset_tsupport g).trans (hgs.trans ball_subset_closedBall))
  exact posterior_query_difference_le_count μ ell j hc hr₀ hs hr₀s hg.continuous hcg
    y z (fun x => hbound hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2) d

end CoulombBarrier

end

end OAI

import OAI.Analysis.LienardCycles.AxisSecants

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
lemma base_strictAnti {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : StrictAntiOn (b a t) (Ioc 0 r) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    (fun s hs=>(base_deriv (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
  intro s hs
  have he' := adm_le he (interior_subset hs).1 (interior_subset hs).2
  rw [(base_deriv he').deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (g_pos he')) (radius_pos he')
lemma rate_model_strictMono {κ s : ℝ} (hs : 0<s) : StrictMono (fun z=>ReferenceCharacteristic.E ((z,κ),s)) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(ReferenceCharacteristic.E_z_deriv (z:=z) (k:=κ) hs).deriv]
  exact mul_pos (ReferenceCharacteristic.K_pos hs) (ReferenceCharacteristic.Az_pos hs)
lemma rate_label {a : Fin 6 → ℝ} {t κ s : ℝ} (he : Adm a t s) :
    ReferenceCharacteristic.E ((label a t κ s,κ),s)=rate a t s := by
  change 2*ReferenceCharacteristic.A ((label a t κ s,κ),s)/(s*(1-ReferenceCharacteristic.A ((label a t κ s,κ),s)^2))=_
  rw [label_spec he]
  rfl
lemma label_factor_pos {a : Fin 6 → ℝ} {t κ s : ℝ} (he : Adm a t s) :
    0<(1-(A a t s)^2)/ReferenceCharacteristic.Az ((label a t κ s,κ),s) := by
  have hh := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mpr (A_abs_lt he)
  have hg : 0<1-(A a t s)^2 := by nlinarith [sq_abs (A a t s)]
  exact div_pos hg (ReferenceCharacteristic.Az_pos (radius_pos he))
lemma not_all_error_neg {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hn : ∀ s ∈ Ioo 0 r, err a t (QuinticFit.kappa a (point a t r)) s<0) : False := by
  let κ := QuinticFit.kappa a (point a t r)
  have hz : StrictAntiOn (label a t κ) (Ioc 0 r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
      (fun s hs=>(label_deriv (κ:=κ) (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [(label_deriv (κ:=κ) (adm_le he hs.1 hs.2.le)).deriv]
    rw [mul_div_assoc]
    exact mul_neg_of_neg_of_pos (hn s hs) (label_factor_pos (adm_le he hs.1 hs.2.le))
  have hp : 0<L a t r-ReferenceCharacteristic.L ((label a t κ r,κ),r) := by
    apply ReferenceCharacteristic.strictMono_zero_pos (f:=fun s=>L a t s-ReferenceCharacteristic.L ((label a t κ r,κ),s)) (radius_pos he)
      (by simpa only [sub_self] using ((small_limits he).2.1.sub
        (ReferenceCharacteristic.L_tendsto_zero (label a t κ r) κ)))
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
      (fun s hs=>((L_deriv (adm_le he hs.1 hs.2)).sub (ReferenceCharacteristic.L_deriv hs.1)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [((L_deriv (adm_le he hs.1 hs.2.le)).sub (ReferenceCharacteristic.L_deriv (z:=label a t κ r) (k:=κ) hs.1)).deriv]
    apply sub_pos.mpr
    rw [←rate_label (κ:=κ) (adm_le he hs.1 hs.2.le)]
    exact rate_model_strictMono hs.1 (hz ⟨hs.1,hs.2.le⟩ ⟨radius_pos he,le_rfl⟩ hs.2)
  rw [L_matched he,sub_self] at hp
  exact (lt_irrefl 0) hp
lemma not_all_error_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hn : ∀ s ∈ Ioo 0 r, 0<err a t (QuinticFit.kappa a (point a t r)) s) : False := by
  let κ := QuinticFit.kappa a (point a t r)
  have hz : StrictMonoOn (label a t κ) (Ioc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
      (fun s hs=>(label_deriv (κ:=κ) (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [(label_deriv (κ:=κ) (adm_le he hs.1 hs.2.le)).deriv]
    rw [mul_div_assoc]
    exact mul_pos (hn s hs) (label_factor_pos (adm_le he hs.1 hs.2.le))
  have hp : 0<ReferenceCharacteristic.L ((label a t κ r,κ),r)-L a t r := by
    apply ReferenceCharacteristic.strictMono_zero_pos (f:=fun s=>ReferenceCharacteristic.L ((label a t κ r,κ),s)-L a t s) (radius_pos he)
      (by simpa only [sub_self] using ((ReferenceCharacteristic.L_tendsto_zero (label a t κ r) κ).sub (small_limits he).2.1))
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
      (fun s hs=>((ReferenceCharacteristic.L_deriv (z:=label a t κ r) (k:=κ) hs.1).sub (L_deriv (adm_le he hs.1 hs.2))).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [((ReferenceCharacteristic.L_deriv (z:=label a t κ r) (k:=κ) hs.1).sub (L_deriv (adm_le he hs.1 hs.2.le))).deriv]
    apply sub_pos.mpr
    rw [←rate_label (κ:=κ) (adm_le he hs.1 hs.2.le)]
    exact rate_model_strictMono hs.1 (hz ⟨hs.1,hs.2.le⟩ ⟨radius_pos he,le_rfl⟩ hs.2)
  rw [L_matched he,sub_self] at hp
  exact (lt_irrefl 0) hp

theorem curvature_lower {a : Fin 6 → ℝ} {t r C : ℝ} (he : Adm a t r)
    (hC : ∀ u ∈ Icc (b a t r) t, C≤ScaledProfile.curvature a u) :
    C≤QuinticFit.kappa a (point a t r) := by
  by_contra! hn
  let κ := QuinticFit.kappa a (point a t r)
  apply not_all_error_neg he
  intro s hs
  have he' := adm_le he hs.1 hs.2.le
  apply ScalarComparison.linear_negative_from_zero hs.1
    (fun u hu=>(coeff_continuous (κ:=κ) (adm_le he' hu.1 hu.2)).continuousWithinAt)
    (fun u hu=>coeff_pos (κ:=κ) (adm_le he' hu.1 hu.2))
    (fun u hu=>err_deriv (κ:=κ) (adm_le he' hu.1 hu.2))
    (fun u hu=>?_) (err_tendsto he κ)
  have heu := adm_le he hu.1 (hu.2.le.trans hs.2.le)
  have hb : b a t r≤b a t u := (base_strictAnti he).antitoneOn
    ⟨hu.1,hu.2.le.trans hs.2.le⟩ ⟨radius_pos he,le_rfl⟩ (hu.2.le.trans hs.2.le)
  exact neg_neg_of_pos (mul_pos (div_pos (g_pos heu) (radius_pos heu))
    (sub_pos.mpr (hn.trans_le (hC _ ⟨hb,(base_spec heu).2.1.le⟩))))

theorem curvature_upper {a : Fin 6 → ℝ} {t r C : ℝ} (he : Adm a t r)
    (hC : ∀ u ∈ Icc (b a t r) t, ScaledProfile.curvature a u≤C) :
    QuinticFit.kappa a (point a t r)≤C := by
  by_contra! hn
  let κ := QuinticFit.kappa a (point a t r)
  apply not_all_error_pos he
  intro s hs
  have he' := adm_le he hs.1 hs.2.le
  have hneg : -err a t κ s<0 := by
    apply ScalarComparison.linear_negative_from_zero (E:=fun u=> -err a t κ u)
      (F:=fun u=>g a t u/u*(c a t u-κ)) hs.1
      (fun u hu=>(coeff_continuous (κ:=κ) (adm_le he' hu.1 hu.2)).continuousWithinAt)
      (fun u hu=>coeff_pos (κ:=κ) (adm_le he' hu.1 hu.2))
      (fun u hu=>?_) (fun u hu=>?_) (by simpa using (err_tendsto he κ).neg)
    · convert! (err_deriv (κ:=κ) (adm_le he' hu.1 hu.2)).neg using 1
      ring
    · have heu := adm_le he hu.1 (hu.2.le.trans hs.2.le)
      have hb : b a t r≤b a t u := (base_strictAnti he).antitoneOn
        ⟨hu.1,hu.2.le.trans hs.2.le⟩ ⟨radius_pos he,le_rfl⟩ (hu.2.le.trans hs.2.le)
      exact mul_neg_of_pos_of_neg (div_pos (g_pos heu) (radius_pos heu))
        (sub_neg.mpr ((hC _ ⟨hb,(base_spec heu).2.1.le⟩).trans_lt hn))
  linarith
end QuinticLienard.ActualCharacteristic

end OAI

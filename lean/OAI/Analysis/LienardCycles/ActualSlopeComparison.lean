import OAI.Analysis.LienardCycles.ActualError

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
lemma c_strictAnti {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    StrictAntiOn (c a t) (Ioc 0 r) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    (fun s hs => (c_deriv (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
  intro s hs
  have he' := adm_le he (interior_subset hs).1 (interior_subset hs).2
  rw [(c_deriv he').deriv]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos (g_pos he')) (radius_pos he'))
    (hthird _ (base_spec he').1)
lemma label_strictAnti_of_error {a : Fin 6 → ℝ} {t r κ : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) (herr : err a t κ r≤0) :
    StrictAntiOn (label a t κ) (Ioc 0 r) := by
  have hn : ∀ {s : ℝ}, 0<s → s<r → err a t κ s<0 := ScalarComparison.error_negative_before (radius_pos he)
    (fun s hs => (coeff_continuous (adm_le he hs.1 hs.2)).continuousWithinAt)
    (fun s hs => coeff_pos (adm_le he hs.1 hs.2))
    (fun s hs => div_pos (g_pos (adm_le he hs.1 hs.2)) hs.1)
    (c_strictAnti he hthird) (fun s hs => err_deriv (adm_le he hs.1 hs.2))
    (err_tendsto he κ) herr
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    (fun s hs => (label_deriv (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ioc] at hs
  have he' := adm_le he hs.1 hs.2.le
  rw [(label_deriv (κ:=κ) he').deriv]
  have hg : 0<1-(A a t s)^2 := by
    have hh := sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1) |>.mpr (A_abs_lt he')
    nlinarith [sq_abs (A a t s)]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (hn hs.1 hs.2) hg)
    (ReferenceCharacteristic.Az_pos (radius_pos he'))
lemma j_eq_lambda {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    j a t (QuinticFit.kappa a (point a t r)) r=QuinticFit.lambda a (point a t r) := by
  apply QuadraticFit.slope_eq (radius_pos he) (m_abs_lt he)
  exact (QuinticFit.spec a (base_spec he).1 (radius_pos he)).1
lemma L_matched {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.L ((label a t (QuinticFit.kappa a (point a t r)) r,
      QuinticFit.kappa a (point a t r)),r)=L a t r := by
  dsimp only [ReferenceCharacteristic.L,ReferenceCharacteristic.D,L]
  rw [label_J he,j_eq_lambda he]
  congr 1
  exact (QuinticFit.spec a (base_spec he).1 (radius_pos he)).2
lemma rate_gt_reference {a : Fin 6 → ℝ} {t r κ s : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) (herr : err a t κ r≤0)
    (hs : 0<s) (hsr : s<r) :
    ReferenceCharacteristic.E ((label a t κ r,κ),s)<rate a t s := by
  have hz := label_strictAnti_of_error he hthird herr ⟨hs,hsr.le⟩ ⟨radius_pos he,le_rfl⟩ hsr
  have hm : StrictMono (fun z=>ReferenceCharacteristic.E ((z,κ),s)) := by
    apply strictMono_of_deriv_pos
    intro z
    rw [(ReferenceCharacteristic.E_z_deriv (z:=z) (k:=κ) hs).deriv]
    exact mul_pos (ReferenceCharacteristic.K_pos hs) (ReferenceCharacteristic.Az_pos hs)
  have hh := hm hz
  change _ < 2*ReferenceCharacteristic.A ((label a t κ s,κ),s)/(s*(1-ReferenceCharacteristic.A ((label a t κ s,κ),s)^2)) at hh
  rw [label_spec (adm_le he hs hsr.le)] at hh
  exact hh

theorem fitted_slope_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    QuinticFit.lambda a (point a t r)<k a t r := by
  let κ := QuinticFit.kappa a (point a t r)
  by_contra! hn
  have herr : err a t κ r≤0 := by
    dsimp only [err,κ]
    rw [j_eq_lambda he]
    linarith
  have hp : 0<L a t r-ReferenceCharacteristic.L ((label a t κ r,κ),r) := by
    apply ReferenceCharacteristic.strictMono_zero_pos (f:=fun s=>L a t s-ReferenceCharacteristic.L ((label a t κ r,κ),s)) (radius_pos he)
      (by simpa only [sub_self] using ((small_limits he).2.1.sub
        (ReferenceCharacteristic.L_tendsto_zero (label a t κ r) κ)))
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
      (fun s hs => ((L_deriv (adm_le he hs.1 hs.2)).sub
        (ReferenceCharacteristic.L_deriv hs.1)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [((L_deriv (adm_le he hs.1 hs.2.le)).sub
      (ReferenceCharacteristic.L_deriv (z:=label a t κ r) (k:=κ) hs.1)).deriv]
    exact sub_pos.mpr (rate_gt_reference he hthird herr hs.1 hs.2)
  rw [L_matched he,sub_self] at hp
  exact (lt_irrefl 0) hp
end QuinticLienard.ActualCharacteristic

namespace QuinticLienard.QuinticFit

theorem lambda_lt_slope {a : Fin 6 → ℝ} {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (hthird : ∀ u, 0<u → 0<ScaledProfile.third a u) : lambda a (h,r)<ScaledProfile.slope a h := by
  let t := PositiveWidth.peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have ht := PositiveWidth.peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,ht.1,ht.2⟩
  have hb : ActualCharacteristic.b a t r=h := PositiveWidth.base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh ht.1 ht.2
  simpa only [ActualCharacteristic.point,ActualCharacteristic.k,hb] using
    ActualCharacteristic.fitted_slope_lt he hthird
end QuinticLienard.QuinticFit

end OAI

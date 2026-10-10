import Mathlib
import OAI.Analysis.CoulombIonization.Localization.UniformObservationNoiseBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservedPosteriorDensity_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation

lemma original_posterior_count_band_bound {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) (j : ℕ) (k : Fin K)
    (hk : j ≤ k.val) {r : ℝ} (hr : 0 < r) (hnoise : Real.sqrt 3*ell k ≤ r/4) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      (∫ x, rawAnnularCount (r/2) (3*r) x ∂originalRawKernel μ ell j (originalDatum ell j z)) ≤
        observedAnnularCount ell k (r/4) (4*r) z := by
  filter_upwards [original_posterior_annular_count_le_observed μ ell hell j k hk (r/2) (3*r)] with z hz
  apply hz.trans
  exact rawAnnularCount_mono (by linarith) (by linarith) _

lemma master_density_count_scale {r : ℝ} (hr : 0 < r) (D T : ℝ) :
    D*r^(-3-3*masterExponent)*(T/r^3) = D*T*r^(-6-3*masterExponent) := by
  have he : T/r^3 = T*r^(-3:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]; rfl
  rw [he]
  calc
    _ = D*T*(r^(-3-3*masterExponent)*r^(-3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

 theorem exists_observed_posterior_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ z ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (4*r) z ≤ T/r^3 →
        ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
          jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y ≤
            D*T*r^(-6-3*masterExponent) := by
  obtain ⟨D,hD,hbound⟩ := exists_posterior_annular_density_constant hg hgs hc hcL
  refine ⟨D,hD,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hrr hrs hnoise
  have hr : 0 < r := hr₀.trans_le hrr
  filter_upwards [original_posterior_count_band_bound μ ell hell j k hk hr hnoise] with z hz
  intro hcount y hy hy2
  exact (hbound μ ell j hr₀ hs hs1 hrr hrs _ y hy hy2).trans
    ((mul_le_mul_of_nonneg_left (hz.trans hcount) (by positivity)).trans_eq
      (master_density_count_scale hr D T))

end CoulombBarrier

end Work_ObservedPosteriorDensity_barrier_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom

lemma widthKernel_query_difference {t : Space → ℝ} (hp : ∀ x, 0 < t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) (x y z : Space) :
    ‖widthKernel t h x y-widthKernel t h x z‖ ≤
      (H:ℝ)*(t x)⁻¹^4*‖y-z‖ := by
  have hd := hh.dist_le_mul ((t x)⁻¹ • (y-x)) ((t x)⁻¹ • (z-x))
  have he : (y-x)-(z-x) = y-z := by abel
  simp only [dist_eq_norm,←smul_sub,he,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (hp x).le)] at hd
  unfold widthKernel
  rw [←mul_sub,norm_mul,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (hp x).le) _)]
  exact (mul_le_mul_of_nonneg_left hd (pow_nonneg (inv_nonneg.mpr (hp x).le) _)).trans_eq (by ring)

lemma widthKernel_ne_zero_width_lower {t : Space → ℝ}
    (ht : LipschitzWith (1/2) t) (hp : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : widthKernel t h x y ≠ 0) : t y/2 ≤ t x := by
  have ha := widthKernel_ne_zero_distance hp hs hx
  have hd := ht.dist_le_mul y x
  have hb : t y-t x ≤ (1/2:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,norm_sub_rev y x,NNReal.coe_div,
      NNReal.coe_one,NNReal.coe_ofNat] using (le_abs_self (t y-t x)).trans hd
  linarith [hp x]

end CoulombAtom

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombBarrier
open CoulombAtom
attribute [local irreducible] masterWidth masterKernel

lemma inverse_fourth_radius_scale {c r : ℝ} (_hc : 0 < c) (hr : 0 < r) :
    (c*r^(1+masterExponent)/2)⁻¹^4 =
      16*c⁻¹^4*r^(-4-4*masterExponent) := by
  rw [inv_div,div_eq_mul_inv,mul_inv_rev,mul_pow,mul_pow,←Real.rpow_neg hr.le,
    ←Real.rpow_mul_natCast hr.le]
  have he : -(1+masterExponent)*(4:ℝ) = -4-4*masterExponent := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  ring

lemma masterKernel_ne_zero_annular {g : Space → ℝ}
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s r : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hs1 : s ≤ 1) (hrr : r₀ ≤ r) {x y : Space} (hy : r ≤ ‖y‖)
    (hy2 : ‖y‖ ≤ 2*r) (hxy : masterKernel c₁ r₀ s g x y ≠ 0) :
    r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3*r := by
  have hr : 0 < r := hr₀.trans_le hrr
  rw [masterKernel_eq_widthKernel hc hr₀ hs g] at hxy
  have hm := widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
    (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y hxy
  simp only [mem_closedBall,dist_eq_norm] at hm
  have ht := masterWidth_radius_upper hc.le hr₀ hs hs1 hrr hy hy2
  have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
  have hd : ‖x-y‖ ≤ r/2 := by nlinarith
  have hl := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hl
  have hu := norm_sub_norm_le x y
  constructor <;> linarith

 theorem exists_master_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ s r : ℝ}, 0 < r₀ → 0 < s → s ≤ 1 →
      r₀ ≤ r → r ≤ s → ∀ x y z : Space,
      r ≤ ‖y‖ → ‖y‖ ≤ 2*r → r ≤ ‖z‖ → ‖z‖ ≤ 2*r →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3*r then 1 else 0) := by
  have hcomp : HasCompactSupport (fun q => (g q)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      (masterProfile_support hgs)
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  refine ⟨(H:ℝ)*16*c₁⁻¹^4,by positivity,?_⟩
  intro r₀ s r hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2
  have hr : 0 < r := hr₀.trans_le hrr
  have hzero : ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ = 0 →
      ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
        ((H:ℝ)*16*c₁⁻¹^4)*r^(-4-4*masterExponent)*‖y-z‖*
          (if r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3*r then 1 else 0) := by
    intro he
    rw [he]
    split_ifs <;> positivity
  by_cases ha : masterKernel c₁ r₀ s g x y = 0 ∧ masterKernel c₁ r₀ s g x z = 0
  · exact hzero (by rw [ha.1,ha.2,sub_self,norm_zero])
  have hex : masterKernel c₁ r₀ s g x y ≠ 0 ∨ masterKernel c₁ r₀ s g x z ≠ 0 := by tauto
  have hax : r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3*r := hex.elim
    (fun h => masterKernel_ne_zero_annular hgs hc hcL hr₀ hs hs1 hrr hy hy2 h)
    (fun h => masterKernel_ne_zero_annular hgs hc hcL hr₀ hs hs1 hrr hz hz2 h)
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

end CoulombBarrier

end

end OAI

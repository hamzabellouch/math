import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma semigroup_increment_bound (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (f : E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖K t f-K s f‖≤‖K |t-s| f-K 0 f‖ := by
  have step : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v →
      ‖K v f-K u f‖≤‖K (v-u) f-K 0 f‖ := by
    intro u v hu huv
    have hv : K v=(K u).comp (K (v-u)) := by
      convert hadd u (v-u) hu (sub_nonneg.mpr huv) using 1
      congr 1
      ring
    have hz : (K u).comp (K 0)=K u := by simpa using (hadd u 0 hu (le_refl 0)).symm
    have hze := congrArg (fun A : E→L[ℂ] E ↦ A f) hz
    change K u (K 0 f)=K u f at hze
    rw [hv,ContinuousLinearMap.comp_apply,← hze,← map_sub]
    exact hnorm u hu _
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using step hs hst
  · rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hts)]
    exact step ht hts

lemma semigroup_continuousOn (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hzero : ∀ f, Tendsto (fun t ↦ K t f) (𝓝 0) (𝓝 (K 0 f))) (f : E) :
    ContinuousOn (fun t ↦ K t f) (Ici 0) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.tendsto_nhds_nhds.mp (hzero f) ε hε
  refine ⟨δ,hδ,fun s hs hst ↦ ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (semigroup_increment_bound K hadd hnorm f ht hs)
  rw [← dist_eq_norm]
  apply hd
  simpa only [Real.dist_eq,sub_zero,abs_abs] using hst

lemma semigroup_clamped_continuous (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hzero : ∀ f, Tendsto (fun t ↦ K t f) (𝓝 0) (𝓝 (K 0 f))) (f : E) :
    Continuous (fun t : ℝ ↦ K (max 0 t) f) :=
  (semigroup_continuousOn K hadd hnorm hzero f).comp_continuous
    (continuous_const.max continuous_id) (fun _ ↦ show max 0 _ ∈ Ici 0 from le_max_left (0:ℝ) _)

def laplaceIntegrand (K : ℝ → E→L[ℂ] E) (f : E) (t : ℝ) : E :=
  Real.exp (-t) • K (max 0 t) f

lemma laplaceIntegrand_continuous (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hzero : ∀ f, Tendsto (fun t ↦ K t f) (𝓝 0) (𝓝 (K 0 f))) (f : E) :
    Continuous (laplaceIntegrand K f) :=
  (Real.continuous_exp.comp continuous_neg).smul
    (semigroup_clamped_continuous K hadd hnorm hzero f)

lemma laplaceIntegrand_integrable (K : ℝ → E→L[ℂ] E)
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) (a : ℝ) :
    IntegrableOn (laplaceIntegrand K f) (Ioi a) := by
  apply ((integrableOn_exp_neg_Ioi a).mul_const ‖f‖).mono'
    (((Real.continuous_exp.comp continuous_neg).smul (hc f)).aestronglyMeasurable)
  exact Eventually.of_forall (fun t ↦ by
    change ‖Real.exp (-t) • K (max 0 t) f‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hnorm _ (le_max_left _ _) f) (Real.exp_nonneg _))

def semigroupLaplace (K : ℝ → E→L[ℂ] E) (f : E) : E :=
  ∫ t in Ioi (0:ℝ), laplaceIntegrand K f t

lemma integral_Ioi_add (F : ℝ → E) (a h : ℝ) :
    (∫ t in Ioi a, F (t+h))=∫ t in Ioi (a+h), F t := by
  have hm := (measurePreserving_add_right (volume : Measure ℝ) h).restrict_preimage
    (measurableSet_Ioi (a := a+h))
  have hs : (fun t : ℝ ↦ t+h) ⁻¹' Ioi (a+h)=Ioi a := by ext t; simp
  rw [hs] at hm
  exact hm.integral_comp (Homeomorph.addRight h).measurableEmbedding F

variable [CompleteSpace E]

omit [CompleteSpace E] in
lemma semigroupLaplace_norm_le (K : ℝ → E→L[ℂ] E)
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    ‖semigroupLaplace K f‖≤‖f‖ := by
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), ‖laplaceIntegrand K f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0:ℝ), Real.exp (-t)*‖f‖ := by
      apply integral_mono_ae (laplaceIntegrand_integrable K hc hnorm f 0).norm
        ((integrableOn_exp_neg_Ioi 0).mul_const ‖f‖)
      exact Eventually.of_forall (fun t ↦ by
        dsimp only [laplaceIntegrand]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hnorm _ (le_max_left _ _) f) (Real.exp_nonneg _))
    _ = ‖f‖ := by rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]

lemma semigroupLaplace_shift (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {h : ℝ} (hh : 0 ≤ h) :
    K h (semigroupLaplace K f)=Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s) := by
  have hi := laplaceIntegrand_integrable K hc hnorm f 0
  have he : K h (semigroupLaplace K f)=
      Real.exp h • ∫ s in Ioi (0:ℝ), laplaceIntegrand K f (s+h) := by
    rw [semigroupLaplace,← (K h).integral_comp_comm hi,← integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hsh : 0 ≤ s+h := add_nonneg hs0 hh
    dsimp only [laplaceIntegrand]
    rw [max_eq_right hs0,max_eq_right hsh,(K h).map_smul_of_tower,
      show s+h=h+s from add_comm s h,hadd h s hh hs0,ContinuousLinearMap.comp_apply,smul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,integral_Ioi_add,zero_add]
  congr 1
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (laplaceIntegrand_integrable K hc hnorm f h)
  exact eq_sub_of_add_eq' hsplit

lemma semigroupLaplace_project (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    K 0 (semigroupLaplace K f)=semigroupLaplace K f := by
  simpa using semigroupLaplace_shift K hadd hc hnorm f (le_refl 0)

lemma semigroupLaplace_difference_tendsto (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    Tendsto (fun h : ℝ ↦ h⁻¹ • (semigroupLaplace K f-K h (semigroupLaplace K f)))
      (𝓝[>] 0) (𝓝 (K 0 f-semigroupLaplace K f)) := by
  have hiC : Continuous (laplaceIntegrand K f) :=
    (Real.continuous_exp.comp continuous_neg).smul (hc f)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := laplaceIntegrand K f) (a := 0) (b := 0)
    (by simp) (hiC.stronglyMeasurableAtFilter volume (𝓝 0)) hiC.continuousAt
  have hder := (Real.hasDerivAt_exp 0).smul
    ((hasDerivAt_const (0:ℝ) (semigroupLaplace K f)).sub hd)
  have hval : laplaceIntegrand K f 0=K 0 f := by simp [laplaceIntegrand]
  change HasDerivAt (fun h : ℝ ↦ Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s))
    (Real.exp 0 • (0-laplaceIntegrand K f 0)+Real.exp 0 •
      (semigroupLaplace K f-∫ s in (0:ℝ)..0, laplaceIntegrand K f s)) 0 at hder
  simp only [Real.exp_zero,intervalIntegral.integral_same,sub_zero,hval,zero_sub,one_smul] at hder
  have hlim := hder.neg.tendsto_slope_zero.mono_left
    (nhdsWithin_mono 0 (show Ioi (0:ℝ) ⊆ {0}ᶜ from fun h hh ↦ ne_of_gt hh))
  have hl : -(-K 0 f+semigroupLaplace K f)=K 0 f-semigroupLaplace K f := by module
  rw [hl] at hlim
  apply hlim.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  change h⁻¹ • (-(Real.exp (0+h) •
    (semigroupLaplace K f-∫ s in (0:ℝ)..(0+h), laplaceIntegrand K f s)) -
    -(Real.exp 0 • (semigroupLaplace K f-∫ s in (0:ℝ)..0, laplaceIntegrand K f s)))=_
  rw [zero_add,Real.exp_zero,intervalIntegral.integral_same,sub_zero,one_smul,
    semigroupLaplace_shift K hadd hc hnorm f (le_of_lt hh)]
  module

lemma semigroupLaplace_norm_sub_le (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖semigroupLaplace K f-K h (semigroupLaplace K f)‖≤
      (2*Real.exp 1)*h*‖f‖ := by
  have hexp : Real.exp h-1≤Real.exp 1*h := by
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-h)) (Real.exp_nonneg h)
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
    have hm2 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hh1) hh
    nlinarith
  have he1 : 1≤Real.exp h := by simpa using Real.exp_le_exp.mpr hh
  have hi : ‖∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖≤h*‖f‖ := by
    have hb : ∀ s ∈ Set.uIoc (0:ℝ) h, ‖laplaceIntegrand K f s‖≤‖f‖ := by
      intro s hs
      rw [Set.uIoc_of_le hh] at hs
      dsimp only [laplaceIntegrand]
      rw [max_eq_right (le_of_lt hs.1),norm_smul,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-s)*‖f‖ := mul_le_mul_of_nonneg_left
          (hnorm s (le_of_lt hs.1) f) (Real.exp_nonneg _)
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right (by
          simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (le_of_lt hs.1))) (norm_nonneg _)
        _ = ‖f‖ := one_mul _
    simpa only [sub_zero,abs_of_nonneg hh,mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [semigroupLaplace_shift K hadd hc hnorm f hh]
  have heq : semigroupLaplace K f-Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s)=
      (1-Real.exp h) • semigroupLaplace K f+
        Real.exp h • ∫ s in (0:ℝ)..h, laplaceIntegrand K f s := by module
  rw [heq]
  calc
    _ ≤ ‖(1-Real.exp h) • semigroupLaplace K f‖+
      ‖Real.exp h • ∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖ := norm_add_le _ _
    _ = (Real.exp h-1)*‖semigroupLaplace K f‖+
      Real.exp h*‖∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonpos (by linarith),abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ (Real.exp 1*h)*‖f‖+Real.exp 1*(h*‖f‖) := by
      apply add_le_add
      · exact mul_le_mul hexp (semigroupLaplace_norm_le K hc hnorm f)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (Real.exp_le_exp.mpr hh1) hi (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

omit [CompleteSpace E] in
lemma laplaceIntegrand_eq_complex (K : ℝ → E→L[ℂ] E) (f : E) (t : ℝ) :
    laplaceIntegrand K f t = (Real.exp (-t) : ℂ) • K (max 0 t) f := by
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

lemma semigroupLaplace_difference_tendsto_complex (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    Tendsto (fun h : ℝ ↦ (h⁻¹ : ℂ) • (semigroupLaplace K f-K h (semigroupLaplace K f)))
      (𝓝[>] 0) (𝓝 (K 0 f-semigroupLaplace K f)) := by
  have hh := semigroupLaplace_difference_tendsto K hadd hc hnorm f
  apply hh.congr
  intro h
  rw [← IsScalarTower.algebraMap_smul ℂ h⁻¹
    (semigroupLaplace K f-K h (semigroupLaplace K f))]
  change ((h⁻¹:ℝ):ℂ) • (semigroupLaplace K f-K h (semigroupLaplace K f)) = _
  rw [Complex.ofReal_inv]

end HardSphere

end

end OAI

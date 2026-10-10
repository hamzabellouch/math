import Mathlib
import OAI.Geometry.WeakHessian.Entropy.SmoothDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

lemma exists_oneSidedKernel {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : ℝ → ℝ,HasCompactSupport κ ∧ ContDiff ℝ 1 κ ∧
      (∀ r,0 ≤ κ r) ∧ (∫ r,κ r) = 1 ∧ Function.support κ ⊆ Icc 0 δ := by
  let f : ContDiffBump (δ/2) := ⟨δ/4,δ/2,by linarith,by linarith⟩
  refine ⟨f.normed volume,f.hasCompactSupport_normed,f.contDiff_normed,
    f.nonneg_normed,f.integral_normed,?_⟩
  rw [f.support_normed_eq]
  intro r hr
  change dist r (δ/2) < δ/2 at hr
  rw [Real.dist_eq,abs_lt] at hr
  constructor <;> linarith [hr.1,hr.2]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma timeAverageLaw_terminal_ball {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : ∀ᵐ s ∂ν,s ∈ Icc 0 δ) {r D : ℝ} (_ : 0 ≤ D)
    (o : X) (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) o ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D) :
    ∀ᵐ x ∂timeAverageLaw π ν 1,dist x o ≤ r+δ*D := by
  apply (ae_map_iff (continuous_timeAverageEval 1).measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  have Hδ : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,z.1 ∈ Icc 0 δ :=
    ae_of_ae_map measurable_fst.aemeasurable (by simpa only [Measure.map_fst_prod,measure_univ,one_smul] using hδ)
  have Hγ : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,IsGeodesic z.2 ∧
      dist (z.2 timeOne) o ≤ r ∧ dist (z.2 timeZero) (z.2 timeOne) ≤ D := by
    exact ae_of_ae_map (μ := ν.prod π) (f := Prod.snd) measurable_snd.aemeasurable
      (by simpa only [Measure.map_snd_prod,measure_univ,one_smul] using hgeo.and (hs.and hl))
  filter_upwards [Hδ,Hγ] with z hz hγ
  change dist (z.2 (clampTime (1-z.1))) o ≤ _
  have ht : |(clampTime (1-z.1):ℝ)-(timeOne:ℝ)| ≤ δ := by
    have ha := (clampTime (1-z.1)).property
    change 0 ≤ max 0 (min 1 (1-z.1)) ∧ max 0 (min 1 (1-z.1)) ≤ 1 at ha
    change |max 0 (min 1 (1-z.1))-1| ≤ δ
    rw [abs_of_nonpos (by linarith : max 0 (min 1 (1-z.1))-1 ≤ 0)]
    have hh : 1-z.1 ≤ max 0 (min 1 (1-z.1)) := by
      rw [min_eq_right (by linarith [hz.1])]
      exact le_max_right _ _
    linarith [hz.2]
  have hd := mul_le_mul ht hγ.2.2 dist_nonneg (le_trans (abs_nonneg _) ht)
  have H := dist_triangle (z.2 (clampTime (1-z.1))) (z.2 timeOne) o
  rw [hγ.1] at H
  linarith [hγ.2.1]

lemma kernelMeasure_ae_support {κ : ℝ → ℝ} (hc : Continuous κ) {S : Set ℝ}
    (hs : Function.support κ ⊆ S) : ∀ᵐ r ∂kernelMeasure κ,r ∈ S := by
  apply (ae_withDensity_iff hc.measurable.ennreal_ofReal).mpr
  exact ae_of_all _ fun r hr => hs (by
    intro hz
    exact hr (by simp only [hz,ENNReal.ofReal_zero]))

end WeakHessian

end
end

end OAI

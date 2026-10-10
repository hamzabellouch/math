import Mathlib
import OAI.Analysis.HardSphere.Comparison.LaplaceIntegrand

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma semigroupLaplace_hasDerivWithinAt (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ K s (semigroupLaplace K f))
      (K t (semigroupLaplace K f)-K t f) (Ici 0) t := by
  have hiC : Continuous (laplaceIntegrand K f) :=
    (Real.continuous_exp.comp continuous_neg).smul (hc f)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := laplaceIntegrand K f) (a := 0) (b := t)
    (hiC.intervalIntegrable 0 t) (hiC.stronglyMeasurableAtFilter volume (𝓝 t)) hiC.continuousAt
  have hder := (Real.hasDerivAt_exp t).smul
    ((hasDerivAt_const t (semigroupLaplace K f)).sub hd)
  have heq : EqOn (fun s : ℝ ↦ Real.exp s •
      (semigroupLaplace K f-∫ z in (0:ℝ)..s,laplaceIntegrand K f z))
      (fun s ↦ K s (semigroupLaplace K f)) (Ici 0) :=
    fun s hs ↦ (semigroupLaplace_shift K hadd hc hnorm f hs).symm
  have hv : Real.exp t • (0-laplaceIntegrand K f t)+
      Real.exp t • (semigroupLaplace K f-∫ z in (0:ℝ)..t,laplaceIntegrand K f z)=
      K t (semigroupLaplace K f)-K t f := by
    rw [← semigroupLaplace_shift K hadd hc hnorm f ht,zero_sub,smul_neg,
      laplaceIntegrand,max_eq_right ht,smul_smul,← Real.exp_add,add_neg_cancel,
      Real.exp_zero,one_smul]
    abel
  change HasDerivAt (fun s : ℝ ↦ Real.exp s •
      (semigroupLaplace K f-∫ z in (0:ℝ)..s,laplaceIntegrand K f z))
    (Real.exp t • (0-laplaceIntegrand K f t)+
      Real.exp t • (semigroupLaplace K f-∫ z in (0:ℝ)..t,laplaceIntegrand K f z)) t at hder
  rw [hv] at hder
  exact hder.hasDerivWithinAt.congr (fun s hs ↦ (heq hs).symm) (heq ht).symm

lemma semigroupLaplace_eigenvector (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E)
    {r : ℝ} (hr : 0<r) (he : semigroupLaplace K f=r • f)
    {t : ℝ} (ht : 0 ≤ t) : K t f=Real.exp ((1-r⁻¹)*t) • f := by
  have hz : K 0 f=f := by
    have hh := semigroupLaplace_project K hadd hc hnorm f
    rw [he,(K 0).map_smul_of_tower] at hh
    exact (smul_right_injective E (ne_of_gt hr)) hh
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt (fun x : ℝ ↦ K x f)
      ((1-r⁻¹) • K s f) (Ici 0) s := by
    have h := (semigroupLaplace_hasDerivWithinAt K hadd hc hnorm f hs).const_smul r⁻¹
    simp only [he,ContinuousLinearMap.map_smul_of_tower] at h
    change HasDerivWithinAt (fun x : ℝ ↦ r⁻¹ • (r • K x f))
       (r⁻¹ • (r • K s f-K s f)) (Ici 0) s at h
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul] at h
    convert h using 1
    module
  let F : ℝ → E := fun x ↦ Real.exp ((r⁻¹-1)*x) • K x f
  have hFcont : ContinuousOn F (Ici 0) := by
    have h : ContinuousOn (fun x : ℝ ↦ Real.exp ((r⁻¹-1)*x) • K (max 0 x) f) (Ici 0) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (hc f)).continuousOn
    exact h.congr (fun s hs ↦ by simp only [F,max_eq_right (show 0 ≤ s from hs)])
  have hdF (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt F 0 (Ici 0) s := by
    have h := (((hasDerivAt_id s).const_mul (r⁻¹-1)).exp.hasDerivWithinAt).smul (hd s hs)
    convert h using 1
    · rfl
    · module
  have hconst := constant_of_has_deriv_right_zero
    (hFcont.mono (Icc_subset_Ici_self : Icc (0:ℝ) t ⊆ Ici 0))
    (fun s hs ↦ (hdF s hs.1).mono (Ici_subset_Ici.mpr hs.1))
  have heF : Real.exp ((r⁻¹-1)*t) • K t f=f := by
    simpa only [F,mul_zero,Real.exp_zero,one_smul,hz] using hconst t ⟨ht,le_refl _⟩
  calc
    K t f=Real.exp ((1-r⁻¹)*t) • (Real.exp ((r⁻¹-1)*t) • K t f) := by
      rw [smul_smul,← Real.exp_add,show (1-r⁻¹)*t+(r⁻¹-1)*t=0 by ring,
        Real.exp_zero,one_smul]
    _ = _ := by rw [heF]

end HardSphere

end

end OAI

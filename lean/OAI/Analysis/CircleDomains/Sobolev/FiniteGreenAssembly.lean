import OAI.Analysis.CircleDomains.Sobolev.LocalizedJordanIntegral

namespace OAI

/-! Finite additivity of the actual boundary integral and curl integral,
and assembly from a smooth partition on the closed Jordan disk. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma planarFormIntegral_finite_sum {ι : Type*} [Fintype ι]
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (A B : ι → ℂ → ℝ)
    (hA : ∀ i, Continuous (A i)) (hB : ∀ i, Continuous (B i)) :
    planarFormIntegral (fun z => ∑ i, A i z) (fun z => ∑ i, B i z) γ =
      ∑ i, planarFormIntegral (A i) (B i) γ := by
  unfold planarFormIntegral
  rw [← intervalIntegral.integral_finsetSum (fun i _ =>
    (planarFormIntegrand_continuous hγ (hA i) (hB i)).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Finset.sum_add_distrib,Finset.sum_mul]

lemma integral_planar_curl_finite_sum {ι : Type*} [Fintype ι]
    (H : ℂ ≃ₜ ℂ) (A B : ι → ℂ → ℝ)
    (hA : ∀ i, ContDiff ℝ ∞ (A i)) (hB : ∀ i, ContDiff ℝ ∞ (B i)) :
    (∫ z in jordanInterior H,
      (fderiv ℝ (fun w => ∑ i, B i w) z) 1 -
        (fderiv ℝ (fun w => ∑ i, A i w) z) Complex.I) =
      ∑ i, ∫ z in jordanInterior H, (fderiv ℝ (B i) z) 1 - (fderiv ℝ (A i) z) Complex.I := by
  have hi (i : ι) : IntegrableOn
      (fun z => (fderiv ℝ (B i) z) 1 - (fderiv ℝ (A i) z) Complex.I) (jordanInterior H) := by
    have hc := ((hB i).continuous_fderiv (by simp)).clm_apply (continuous_const (y := (1 : ℂ)))
    have hd := ((hA i).continuous_fderiv (by simp)).clm_apply (continuous_const (y := Complex.I))
    exact ((hc.sub hd).continuousOn.integrableOn_compact
      (isCompact_closure_jordanInterior H)).mono_set subset_closure
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply setIntegral_congr_fun (jordanInterior_isOpen H).measurableSet
  intro z _
  dsimp only
  rw [fderiv_fun_sum (fun i _ => (hB i).differentiable (by simp) z),
    fderiv_fun_sum (fun i _ => (hA i).differentiable (by simp) z)]
  simp only [_root_.sum_apply,Finset.sum_sub_distrib]

lemma finite_green_assembly {ι : Type*} [Fintype ι]
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (ρ : ι → ℂ → ℝ) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hsum : ∀ z ∈ closure (jordanInterior H), ∑ i, ρ i z = 1)
    (ε : ℝ) {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hlocal : ∀ i, ε * planarFormIntegral (fun z => ρ i z * P z) (fun z => ρ i z * Q z) γ =
      ∫ z in jordanInterior H,
        (fderiv ℝ (fun w => ρ i w * Q w) z) 1 -
          (fderiv ℝ (fun w => ρ i w * P w) z) Complex.I) :
    ε * planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  let A := fun i z => ρ i z * P z
  let B := fun i z => ρ i z * Q z
  have hA (i : ι) : ContDiff ℝ ∞ (A i) := (hρ i).mul hP
  have hB (i : ι) : ContDiff ℝ ∞ (B i) := (hρ i).mul hQ
  have hsumF (f : ℂ → ℝ) (z : ℂ) (hz : z ∈ closure (jordanInterior H)) :
      (∑ i, ρ i z * f z) = f z := by rw [← Finset.sum_mul,hsum z hz,one_mul]
  have hb : planarFormIntegral (fun z => ∑ i, A i z) (fun z => ∑ i, B i z) γ =
      planarFormIntegral P Q γ := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hsumF P _ (hγ.mem_frontier t).1,hsumF Q _ (hγ.mem_frontier t).1]
  have heq (f : ℂ → ℝ) (z : ℂ) (hz : z ∈ jordanInterior H) :
      (fun w => ∑ i, ρ i w * f w) =ᶠ[𝓝 z] f := by
    filter_upwards [(jordanInterior_isOpen H).mem_nhds hz] with w hw
    exact hsumF f w (subset_closure hw)
  have ha : (∫ z in jordanInterior H,
      (fderiv ℝ (fun w => ∑ i, B i w) z) 1 -
        (fderiv ℝ (fun w => ∑ i, A i w) z) Complex.I) =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    apply setIntegral_congr_fun (jordanInterior_isOpen H).measurableSet
    intro z hz
    change (fderiv ℝ (fun w => ∑ i, ρ i w * Q w) z) 1 -
      (fderiv ℝ (fun w => ∑ i, ρ i w * P w) z) Complex.I = _
    rw [(heq Q z hz).fderiv_eq,(heq P z hz).fderiv_eq]
  rw [← hb,planarFormIntegral_finite_sum hγ.smooth A B
      (fun i => (hA i).continuous) (fun i => (hB i).continuous),Finset.mul_sum]
  change (∑ i, ε * planarFormIntegral (fun z => ρ i z * P z)
    (fun z => ρ i z * Q z) γ) = _
  simp_rw [hlocal]
  exact (integral_planar_curl_finite_sum H A B hA hB).symm.trans ha

end CircleDomainRigidity

end

end OAI

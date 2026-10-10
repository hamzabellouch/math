import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.TrialBlowup
import OAI.Analysis.BiholderTransport.Contact.AEContacts
import OAI.Analysis.BiholderTransport.Contact.BranchContact

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section UpperTest
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma active_nonconjugate_of_smooth_upper_test {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x)
    {φ : TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0=cTransform v x)
    (hupper : ∀ᶠ h in 𝓝 0, cTransform v (riemannianExp x h)≤φ h) :
    Function.Injective (fderiv ℝ (fun q => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x q)) p) := by
  have hcoord := mfderiv_comp p (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,Model n)) (mem_chart_source (Model n) (riemannianExp x p)))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv,mfderiv_extChartAt_self] at hcoord
  change fderiv ℝ _ p=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
    𝓘(ℝ,Model n) (riemannianExp x) p at hcoord
  simp only [Function.comp_def] at hcoord
  erw [hcoord]
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro k hk
  by_contra hk0
  have hpair : inner ℝ k k≠0 := by
    rw [real_inner_self_eq_norm_sq]
    exact (sq_pos_of_pos (norm_pos_iff.mpr hk0)).ne'
  have hblow := conjugate_radial_hessian_tendsto_atBot hp.1 hk hpair
  let B := fderiv ℝ (fderiv ℝ φ) 0 k k
  have hlow : ∀ᶠ r : ℝ in 𝓝[<] 1, -|B|≤hessianValue x (r • p) k := by
    filter_upwards [(eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
      nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hr1
    have hID := contracted_minimizer_mem_injectivityDomain hp.1 hr hr1
    let F := fun h => (φ h-φ 0)-(-r⁻¹)*(normalCost x (r • p) h-normalCost x (r • p) 0)
    have hC : ContDiffAt ℝ 2 (normalCost x (r • p)) 0 :=
      (normalCost_contDiffAt hID).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hF : ContDiffAt ℝ 2 F 0 :=
      (hφ.sub contDiffAt_const).sub (contDiffAt_const.mul (hC.sub contDiffAt_const))
    have hm : IsLocalMin F 0 := by
      filter_upwards [hupper] with h hh
      have hs := active_split_lower_support hv hp.1 hp.2 hr hr1 (riemannianExp x h)
      change F 0≤F h
      have he : F h=φ h-cTransform v x+
          (cost (riemannianExp x h) (riemannianExp x (r • p))-
            cost x (riemannianExp x (r • p)))/r := by
        simp only [F,normalCost,riemannianExp_zero,hφ0,div_eq_mul_inv]
        ring
      rw [show F 0=0 by simp [F],he]
      rw [neg_div] at hs
      linarith
    have H := localMin_hessian_nonneg hF hm k
    have He := second_fderiv_scaled_differences hφ hC 1 (-r⁻¹) k
    simp only [one_mul] at He
    change fderiv ℝ (fderiv ℝ F) 0 k k=_ at He
    rw [He] at H
    change 0≤B-(-r⁻¹)*normalHessian x (r • p) k k at H
    rw [←hessianValue_eq_normalHessian hID] at H
    have H' : 0≤B+hessianValue x (r • p) k/r := by
      simpa only [B,normalHessian,neg_mul,sub_neg_eq_add,div_eq_mul_inv,mul_comm] using H
    have Hb : r*B≤|B| := by
      calc
        r*B≤r*|B| := mul_le_mul_of_nonneg_left (le_abs_self _) hr.le
        _≤1*|B| := mul_le_mul_of_nonneg_right hr1.le (abs_nonneg _)
        _=|B| := one_mul _
    have H'' := (le_div_iff₀ hr).mp (show -B≤hessianValue x (r • p) k/r by linarith)
    nlinarith
  have hlt := hblow.eventually (eventually_lt_atBot (-|B|))
  obtain ⟨r,hr,hr'⟩ := (hlow.and hlt).exists
  exact (not_lt_of_ge hr) hr'

omit [MeasurableSpace M] [BorelSpace M] in
lemma active_before_cut_of_differentiable_upper_test {v : M → ℝ} (hv : Continuous v)
    {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {φ : TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0=cTransform v x)
    (hupper : ∀ᶠ h in 𝓝 0, cTransform v (riemannianExp x h)≤φ h)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x) :
    p∈injectivityDomain x := by
  apply mem_injectivityDomain_of_unique_nonconjugate _
    (active_nonconjugate_of_smooth_upper_test hv hp hφ hφ0 hupper)
  intro q hq heq
  have hqA : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hp.2⟩
  have H := (active_log_derivative hv hDiff hqA).unique (active_log_derivative hv hDiff hp)
  apply ext_inner_right ℝ
  intro h
  exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H

end UpperTest
end WeakMTWTransport

end

end

end

end OAI

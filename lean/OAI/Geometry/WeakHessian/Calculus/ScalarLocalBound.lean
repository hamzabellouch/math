import Mathlib
import OAI.Geometry.WeakHessian.Calculus.ScalarSecondDifference

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma integral_second_deriv_le_of_local_differences {f q φ : ℝ → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 → secondDifference f h x ≤ q x+ε)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0:ℝ) 1) (hnn : ∀ x,0 ≤ φ x) :
    (∫ x,f x*deriv (deriv φ) x) ≤ ∫ x,q x*φ x := by
  have H (ε : ℝ) (hε : 0 < ε) :
      (∫ x,f x*deriv (deriv φ) x) ≤ (∫ x,q x*φ x)+ε*(∫ x,φ x) := by
    obtain ⟨δ,hδ,hbound⟩ := hlocal ε hε
    obtain ⟨η,hη,hηs⟩ := hc.exists_thickening_subset_open isOpen_Ioo hs
    have hi : Integrable (fun x => q x*φ x) := (hq.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
    have he : (∫ x,(q x+ε)*φ x) = (∫ x,q x*φ x)+ε*(∫ x,φ x) := by
      simp_rw [add_mul]
      rw [integral_add hi (hj.const_mul ε),integral_const_mul]
    rw [← he]
    apply le_of_tendsto_of_tendsto
      ((integral_secondDifference_tendsto hf hφ hc hs).mono_left (nhdsGT_le_nhdsNE 0)) tendsto_const_nhds
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,|h| < η ∧ h < δ := by
      filter_upwards [(eventually_abs_sub_lt (0:ℝ) hη).filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hh'
      exact ⟨by simpa only [sub_zero] using hh,hh'⟩
    filter_upwards [hsmall,self_mem_nhdsWithin] with h hh (hhpos : 0 < h)
    rw [integral_mul_secondDifference hf hφ.continuous hc]
    have hdf : Continuous (fun x => secondDifference f h x) := by
      dsimp only [secondDifference]
      fun_prop
    apply integral_mono
      ((hdf.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (((hq.add continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left)
    intro x
    change secondDifference f h x*φ x ≤ (q x+ε)*φ x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero,le_refl]
    have hxs : x ∈ tsupport φ := subset_closure hx
    have hp : x+h ∈ Ioo (0:ℝ) 1 := by
      apply hηs
      apply Metric.mem_thickening_iff.mpr
      exact ⟨x,hxs,by simpa only [Real.dist_eq,add_sub_cancel_left] using hh.1⟩
    have hm : x-h ∈ Ioo (0:ℝ) 1 := by
      apply hηs
      apply Metric.mem_thickening_iff.mpr
      exact ⟨x,hxs,by simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg] using hh.1⟩
    exact mul_le_mul_of_nonneg_right (hbound h hhpos hh.2 x hm hp) (hnn x)
  have hlim : Tendsto (fun ε : ℝ => (∫ x,q x*φ x)+ε*(∫ x,φ x)) (𝓝[>] 0) (𝓝 (∫ x,q x*φ x)) := by
    convert (show ContinuousAt (fun ε : ℝ => (∫ x,q x*φ x)+ε*(∫ x,φ x)) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact H ε hε

lemma setIntegral_second_deriv_le_of_local_differences {f q φ : ℝ → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 → secondDifference f h x ≤ q x+ε)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0:ℝ) 1) (hnn : ∀ x,0 ≤ φ x) :
    (∫ x in Icc (0:ℝ) 1,f x*deriv (deriv φ) x) ≤ ∫ x in Icc (0:ℝ) 1,q x*φ x := by
  have he₁ : (∫ x in Icc (0:ℝ) 1,f x*deriv (deriv φ) x) = ∫ x,f x*deriv (deriv φ) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (deriv (deriv φ)) := by
      intro hp
      have hxp := hs (tsupport_deriv_subset (tsupport_deriv_subset hp))
      exact hx ⟨hxp.1.le,hxp.2.le⟩
    rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]
  have he₂ : (∫ x in Icc (0:ℝ) 1,q x*φ x) = ∫ x,q x*φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport φ := fun hp => hx ⟨(hs hp).1.le,(hs hp).2.le⟩
    rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]
  rw [he₁,he₂]
  exact integral_second_deriv_le_of_local_differences hf hq hlocal hφ hc hs hnn
end WeakHessian

end
end

end OAI

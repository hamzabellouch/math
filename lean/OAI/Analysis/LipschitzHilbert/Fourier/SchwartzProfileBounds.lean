import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelComparison
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! The endpoint assumptions in the sharp truncation comparison follow
from Schwartz regularity and the single normalization value at zero. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzProfile_bounds (a : SchwartzMap ℝ ℂ) (ha : a 0= -1) :
    ∃ D : ℝ, 0≤D ∧ (∀ s, ‖a s+1‖≤D*|s|) ∧ (∀ s, |s| *‖a s‖≤D) := by
  let D := SchwartzMap.seminorm ℝ 0 1 a+SchwartzMap.seminorm ℝ 1 0 a
  have h0 : 0≤SchwartzMap.seminorm ℝ 0 1 a := apply_nonneg _ _
  have h1 : 0≤SchwartzMap.seminorm ℝ 1 0 a := apply_nonneg _ _
  have hd (x : ℝ) : ‖deriv a x‖≤SchwartzMap.seminorm ℝ 0 1 a := by
    simpa only [pow_zero,one_mul,iteratedDeriv_one] using a.le_seminorm' ℝ 0 1 x
  refine ⟨D,add_nonneg h0 h1,?_,?_⟩
  · intro s
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x∈(Set.univ : Set ℝ)) => a.differentiableAt)
      (fun x (_ : x∈(Set.univ : Set ℝ)) => hd x) (Set.mem_univ (0:ℝ)) (Set.mem_univ s)
    rw [ha,sub_neg_eq_add,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h1) (abs_nonneg s))
  · intro s
    have h := a.norm_pow_mul_le_seminorm ℝ 1 s
    simp only [pow_one,Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left h0)

theorem schwartzFiniteTimeKernel_sharp_integral (k a : SchwartzMap ℝ ℂ)
    (ha : a 0= -1) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2)) :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t‖)≤B := by
  obtain ⟨D,hD,hnear,hfar⟩ := schwartzProfile_bounds a ha
  refine ⟨8*Real.pi*D,by positivity,?_⟩
  intro N topLength htop
  exact finiteTimeKernel_sharp_integral k a a.continuous.measurable hprofile
    D hD hnear hfar N topLength htop

end LipschitzHilbert.PacketRepresentation

end

end OAI

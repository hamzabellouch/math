import OAI.InformationTheory.SoftChannel.Window

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma continuousAt_rSecondDeriv {s : ℝ} (hs : s ∈ Ioo (0:ℝ) ell) :
    ContinuousAt rSecondDeriv s := by
  have hu := psiInv_mem_Ioo hs
  have hi := continuousAt_psiInv hs
  have ht := (hasDerivAt_artanh ⟨by linarith [hu.1],hu.2⟩).continuousAt.comp hi
  have ht0 : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq0 : 1-(psiInv s)^2 ≠ 0 := by nlinarith [hu.1,hu.2]
  have hc := (((continuousAt_const (y := (1:ℝ))).add (hi.pow 2)).mul ht |>.sub hi).div
    (((continuousAt_const.sub (hi.pow 2)).pow 2).mul (ht.pow 3))
    (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ ht0))
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs.1] with x hx
  simp [rSecondDeriv,ite_eq_right (not_le.mpr (show 0<x from hx))]

lemma rate_window_point {u b : ℝ} (hu : u ∈ Ioo (0:ℝ) ell) :
    -(2/3:ℝ)*clipKernel b (ell-u) ≤ (u-(ell-b))*rSecondDeriv u := by
  have hsec := (rSecondDeriv_pos hu).le
  have hs : 0 < ell-u := by linarith [hu.2]
  by_cases h : ell-u ≤ b
  · rw [clipKernel_of_le h,mul_zero]
    exact mul_nonneg (by linarith) hsec
  · have hb : b < ell-u := lt_of_not_ge h
    rw [clipKernel_eq hb.le]
    have hupper : rSecondDeriv u ≤ (2/3:ℝ)/(ell-u)^2 := by
      exact (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by
        simpa only [mul_comm] using inverseEntropy_curvature_bound hu)
    have hm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ ell-u-b by linarith)
    convert! neg_le_neg hm using 1 <;> ring

lemma rate_window_euler {v I b k : ℝ} (hv : 0 < v) (hvI : v ≤ I) (hI : I < ell)
    (hk : 0 ≤ k)
    (hwindow : (∫ h in (ell-I)..(ell-v), clipKernel b h) ≤ 3*k) :
    0 ≤ ((I-(ell-b))*rDeriv I-r I)-((v-(ell-b))*rDeriv v-r v)+rDeriv v*k := by
  have hdom : ∀ u ∈ uIcc v I, u ∈ Ioo (0:ℝ) ell := by
    intro u hu
    rw [uIcc_of_le hvI] at hu
    exact ⟨hv.trans_le hu.1,hu.2.trans_lt hI⟩
  have hfc : ContinuousOn (fun u => (u-(ell-b))*rSecondDeriv u) (uIcc v I) := by
    intro u hu
    exact ((continuousAt_id.sub continuousAt_const).mul
      (continuousAt_rSecondDeriv (hdom u hu))).continuousWithinAt
  have hkc : ContinuousOn (fun u => -(2/3:ℝ)*clipKernel b (ell-u)) (uIcc v I) := by
    intro u hu
    exact (continuousAt_const.mul ((continuousAt_clipKernel b (by dsimp; linarith [(hdom u hu).2])).comp
      (continuousAt_const.sub continuousAt_id))).continuousWithinAt
  have hder : ∀ u ∈ uIcc v I,
      HasDerivAt (fun z => (z-(ell-b))*rDeriv z-r z) ((u-(ell-b))*rSecondDeriv u) u := by
    intro u hu
    convert! (((hasDerivAt_id u).sub_const (ell-b)).mul (hasDerivAt_rDeriv (hdom u hu))).sub
      (hasDerivAt_r (hdom u hu)) using 1; dsimp; ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hfc.intervalIntegrable
  have hcomp := intervalIntegral.integral_mono_on (μ := volume) hvI hkc.intervalIntegrable hfc.intervalIntegrable
    (fun u hu => rate_window_point (hdom u (by rwa [uIcc_of_le hvI])))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left] at hcomp
  rw [heq] at hcomp
  have hsl := mul_le_mul_of_nonneg_right (rDeriv_ge_two hv.le (hvI.trans_lt hI)) hk
  nlinarith

end LeanBlast.CourtadeKumar
end
end

end OAI

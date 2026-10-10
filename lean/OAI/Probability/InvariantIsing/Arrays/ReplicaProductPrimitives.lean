import OAI.Probability.InvariantIsing.Arrays.QuantileProductPath
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace OAI

/-! Integral primitive identities for bounded measurable replica paths.
No continuity of the overlap paths is required. -/

noncomputable section

open MeasureTheory Set Filter

namespace InvariantIsing

lemma absolutelyContinuous_tail_integral {f : ℝ → ℝ} {s t : ℝ}
    (hf : IntervalIntegrable f volume s t) :
    AbsolutelyContinuousOnInterval (fun u => ∫ v in u..t, f v) s t := by
  have he := (hf.absolutelyContinuousOnInterval_intervalIntegral (c := t) (by simp)).neg
  convert he using 1
  funext u
  rw [intervalIntegral.integral_symm t u]
  rfl

lemma continuous_tail_integral {f : ℝ → ℝ}
    (hf : ∀ s t, IntervalIntegrable f volume s t) (t : ℝ) :
    Continuous (fun u => ∫ v in u..t, f v) := by
  have he := (intervalIntegral.continuous_primitive hf t).neg
  convert he using 1
  funext u
  rw [intervalIntegral.integral_symm t u]
  rfl

lemma ae_hasDerivAt_tail_integral {f : ℝ → ℝ} {s t : ℝ}
    (hf : IntervalIntegrable f volume s t) :
    ∀ᵐ u, u ∈ uIcc s t → HasDerivAt (fun u => ∫ v in u..t, f v) (-f u) u := by
  filter_upwards [hf.ae_hasDerivAt_integral] with u hu hmem
  have he := (hu hmem t (by simp)).neg
  convert he using 1
  funext w
  rw [intervalIntegral.integral_symm t w]
  rfl

lemma integral_tail_product {a b : ℝ → ℝ} {s t : ℝ}
    (ha : IntervalIntegrable a volume s t) (hb : IntervalIntegrable b volume s t) :
    (∫ u in s..t, a u * (∫ v in u..t, b v) + b u * (∫ v in u..t, a v)) =
      (∫ u in s..t, a u) * (∫ u in s..t, b u) := by
  let A : ℝ → ℝ := fun u => ∫ v in u..t, a v
  let B : ℝ → ℝ := fun u => ∫ v in u..t, b v
  have hA : AbsolutelyContinuousOnInterval A s t := absolutelyContinuous_tail_integral ha
  have hB : AbsolutelyContinuousOnInterval B s t := absolutelyContinuous_tail_integral hb
  have he := hA.integral_deriv_mul_eq_sub hB
  have hneg : (∫ u in s..t, a u * B u + b u * A u) =
      -(∫ u in s..t, deriv A u * B u + A u * deriv B u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_hasDerivAt_tail_integral ha, ae_hasDerivAt_tail_integral hb] with u hua hub hu
    have hm := uIoc_subset_uIcc hu
    have hda : deriv A u = -a u := (hua hm).deriv
    have hdb : deriv B u = -b u := (hub hm).deriv
    rw [hda, hdb]
    ring
  have hAt : A t = 0 := by simp [A]
  have hBt : B t = 0 := by simp [B]
  rw [hAt, hBt, zero_mul, zero_sub] at he
  rw [he, neg_neg] at hneg
  exact hneg

lemma integral_head_moment {f : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hf : IntervalIntegrable f volume 0 1) :
    (∫ u in s..1, u * f u + ∫ v in 0..u, f v) =
      (∫ u in 0..1, f u) - s * ∫ u in 0..s, f u := by
  let F : ℝ → ℝ := fun u => ∫ v in 0..u, f v
  have hF₀ : AbsolutelyContinuousOnInterval F 0 1 :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hF : AbsolutelyContinuousOnInterval F s 1 := hF₀.mono (by
    rw [uIcc_of_le hs.2, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hs.1 le_rfl)
  have hid : AbsolutelyContinuousOnInterval (fun u : ℝ => u) s 1 :=
    (LipschitzWith.id.lipschitzOnWith).absolutelyContinuousOnInterval
  have he := hid.integral_deriv_mul_eq_sub hF
  have hc : (∫ u in s..1, u * f u + F u) =
      ∫ u in s..1, deriv (fun u : ℝ => u) u * F u + u * deriv F u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_hasDerivAt_integral] with u hu humem
    have hm : u ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]
      have h := humem
      rw [uIoc_of_le hs.2] at h
      exact ⟨hs.1.trans h.1.le, h.2⟩
    have hd : deriv F u = f u := (hu hm 0 (by simp)).deriv
    rw [hd, deriv_id'']
    ring
  rw [hc, he]
  simp only [one_mul, F]

end InvariantIsing

end

end OAI

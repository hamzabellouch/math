import OAI.MeasureTheory.Falconer.Recursion.ProfileSuffixMinimum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI

/-! # Positive slopes of the future minimum occur at contact points -/

namespace Falconer
open Set Filter
open scoped Topology

theorem profileSuffixMinimum_locally_constant_of_gap {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {A : ℝ} (hA : A ∈ Ioo 0 1)
    (hgap : profileSuffixMinimum f A < f A) :
    profileSuffixMinimum f =ᶠ[𝓝 A] fun _ => profileSuffixMinimum f A := by
  obtain ⟨w,hw,he,_⟩ := profileSuffixMinimum_attained hf ⟨hA.1.le,hA.2.le⟩
  have hAw : A < w := by
    by_contra hn
    have heq : w = A := le_antisymm (le_of_not_gt hn) hw.1
    rw [heq] at he
    linarith
  have hcA : ContinuousAt f A := hf.continuousAt (Icc_mem_nhds hA.1 hA.2)
  obtain ⟨η,hη,hclose⟩ := Metric.continuousAt_iff.mp hcA
    ((f A-profileSuffixMinimum f A)/2) (by linarith)
  have hnear : ∀ᶠ u in 𝓝 A, u ∈ Ioo 0 w ∧ dist u A < η := by
    filter_upwards [Ioo_mem_nhds hA.1 hAw,Metric.ball_mem_nhds A hη] with u hu hb
    exact ⟨hu,hb⟩
  filter_upwards [hnear] with u hu
  have huI : u ∈ Icc 0 1 := ⟨hu.1.1.le,(hu.1.2.le.trans hw.2)⟩
  apply le_antisymm
  · rw [he]
    exact profileSuffixMinimum_le hf huI ⟨hu.1.2.le,hw.2⟩
  · obtain ⟨z,hz,hez,_⟩ := profileSuffixMinimum_attained hf huI
    rw [hez]
    by_cases hAz : A ≤ z
    · exact profileSuffixMinimum_le hf ⟨hA.1.le,hA.2.le⟩ ⟨hAz,hz.2⟩
    · have hzA : z < A := lt_of_not_ge hAz
      have hd : dist z A < η := by
        rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hzA)]
        have huabs : |u-A| < η := by simpa only [Real.dist_eq] using hu.2
        have hh' := (neg_le_abs (u-A)).trans_lt huabs
        linarith [hz.1]
      have hc := hclose hd
      rw [Real.dist_eq] at hc
      have hh := (neg_le_abs (f z-f A)).trans_lt hc
      linarith

theorem profileSuffixMinimum_contact_of_pos_deriv {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {A l : ℝ} (hA : A ∈ Ioo 0 1)
    (hd : HasDerivAt (profileSuffixMinimum f) l A) (hl : 0 < l) :
    profileSuffixMinimum f A = f A := by
  have hle := profileSuffixMinimum_le hf ⟨hA.1.le,hA.2.le⟩ ⟨le_rfl,hA.2.le⟩
  apply le_antisymm hle
  by_contra hn
  have he := profileSuffixMinimum_locally_constant_of_gap hf hA (lt_of_not_ge hn)
  have hz : HasDerivAt (profileSuffixMinimum f) 0 A :=
    (hasDerivAt_const A (profileSuffixMinimum f A)).congr_of_eventuallyEq he
  have hh := hd.unique hz
  linarith

end Falconer

end OAI

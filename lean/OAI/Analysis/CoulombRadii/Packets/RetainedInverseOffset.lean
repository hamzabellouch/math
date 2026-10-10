import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationPatchScale
import OAI.Analysis.CoulombRadii.RandomFields.ObservationDyadicWidth

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def retainedInverseOffset (D r : ℝ) : ℝ :=
  D+(4/3:ℝ)*inverseObservationOffset 0 r

lemma retainedInverseOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => retainedInverseOffset D r*r^(349/50:ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have H := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<349/50)).const_mul D).add
    ((inverseObservationOffset_scaled_tendsto 0).const_mul (4/3:ℝ))
  simp only [mul_zero,add_zero] at H
  convert H using 1
  funext r
  unfold retainedInverseOffset
  ring

lemma retainedInverseOffset_nonneg {D r : ℝ} (hD : 0≤D) (hr : 0<r) (hr1 : r≤1) :
    0≤retainedInverseOffset D r :=
  add_nonneg hD (mul_nonneg (by norm_num) (inverseObservationOffset_nonneg (by rfl) hr hr1))

lemma exists_retainedInverseOffset_small {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
    ∃ s : ℝ, 0<s ∧ s≤1 ∧ ∀ {r a : ℝ}, 0<r → r<s → 0<a → a≤A*r →
      retainedInverseOffset D r≤a^(-349/50:ℝ) := by
  have ht := (retainedInverseOffset_scaled_tendsto D).mul_const (A^(349/50:ℝ))
  simp only [zero_mul] at ht
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      r<1 ∧ retainedInverseOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ)<1 := by
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
      ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hh
    exact ⟨hr,hh⟩
  obtain ⟨s,hs,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min s 1,lt_min hs (by norm_num),min_le_right _ _,?_⟩
  intro r a hr hrs ha haA
  obtain ⟨hr1,hh⟩ := hsub ⟨hr,hrs.trans_le (min_le_left _ _)⟩
  have hδ := retainedInverseOffset_nonneg hD hr hr1.le
  have hm : retainedInverseOffset D r*a^(349/50:ℝ)≤1 := by
    calc
      _ ≤ retainedInverseOffset D r*(A*r)^(349/50:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le haA (by norm_num)) hδ
      _ = retainedInverseOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ) := by
        rw [Real.mul_rpow hA.le hr.le]; ring
      _ ≤ 1 := hh.le
  rw [neg_div,Real.rpow_neg ha.le,inv_eq_one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr hm

lemma retained_event_offset_le {r₀ D p : ℝ} (hr₀ : 0<r₀) (J j : ℕ)
    (hp : (r₀*2^j)^42≤p) (hp1 : p≤1) :
    D+observationEventEnergyConstant*
      observationWidthSquareSum (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))*
      (1-Real.log p)^5≤retainedInverseOffset D (r₀*2^j) := by
  have hr : 0<r₀*2^j := by positivity
  have hp0 : 0<p := (pow_pos hr _).trans_le hp
  have hm := observationEventOffset_mono_probability
    (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ)) D
    (pow_pos hr 42) hp hp1
  have hl : Real.log ((r₀*2^j)^42)≤0 :=
    Real.log_nonpos (pow_pos hr 42).le (hp.trans hp1)
  have hw := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (observationWidthSquareSum_retained_dyadic hr₀ J j)
      observationEventEnergyConstant_pos.le)
    (pow_nonneg (by linarith : 0≤1-Real.log ((r₀*2^j)^42)) 5)
  unfold retainedInverseOffset inverseObservationOffset
  linarith

end NeutralAtom
end

end

end OAI

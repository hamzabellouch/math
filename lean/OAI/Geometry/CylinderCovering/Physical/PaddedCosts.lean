import OAI.Geometry.CylinderCovering.Physical.CostVariants

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RadialPhysical
open CylinderCovering

lemma centered_padded_cost_eq {b : ℝ} (hb : 0 < b) (η m : ℝ) :
    scaledCost b η (fun s => 1+η^2*(s^4+b^2*s^2)/2+η^2*b^4*m) =
      (2*b*height b) * RadialCaps.Q
        (fun r => 1+effectiveTilt b η^2*(RadialCaps.H r+m)) (effectiveTilt b η) := by
  rw [centeredCost_dictionary hb, canonicalCost_eq_Q]
  congr 2
  funext r
  unfold effectiveTilt RadialCaps.H
  ring

theorem centered_padding_strict {b : ℝ} (hb : 0 < b) (m : ℝ → ℝ)
    (hm : ContinuousAt m 0) (hm0 : m 0 = 0)
    (hmpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 ≤ m η) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      scaledCost b η (fun s => 1+η^2*(s^4+b^2*s^2)/2+η^2*b^4*m η) < 2*b*height b := by
  have hs : ∀ᶠ η : ℝ in 𝓝 0, 12*effectiveTilt b η^2 < 1 :=
    (show ContinuousAt (fun η : ℝ => 12*effectiveTilt b η^2) 0 by
      unfold effectiveTilt; fun_prop).eventually_lt continuousAt_const (by simp [effectiveTilt])
  have h1 : ∀ᶠ η : ℝ in 𝓝 0, m η < 1 :=
    hm.eventually_lt continuousAt_const (by rw [hm0]; norm_num)
  have hg : ∀ᶠ η : ℝ in 𝓝 0, 216*effectiveTilt b η^2+2*m η < 1/30 :=
    (show ContinuousAt (fun η : ℝ => 216*effectiveTilt b η^2+2*m η) 0 from
      (by unfold effectiveTilt; fun_prop)).eventually_lt continuousAt_const
        (by simp [effectiveTilt, hm0])
  filter_upwards [eventually_mem_nhdsWithin, hmpos,
    hs.filter_mono nhdsWithin_le_nhds, h1.filter_mono nhdsWithin_le_nhds,
    hg.filter_mono nhdsWithin_le_nhds] with η hη hmpos hs h1 hg
  have hηpos : 0 < η := hη
  have he : 0 < effectiveTilt b η := by unfold effectiveTilt; positivity
  have hp := RadialCaps.padded_cost_remainder (ε := effectiveTilt b η)
    (c := 1) hmpos h1.le (by norm_num) (by nlinarith only [hs])
  have hcost : RadialCaps.Q (fun r => 1+effectiveTilt b η^2*(RadialCaps.H r+m η))
      (effectiveTilt b η) < 1 := by
    apply RadialCaps.strict_of_remainder he (a := 1/30-2*m η) (K := 216)
    · have heq : 1-(1/30-2*m η)*effectiveTilt b η^2 =
          1+(2*m η-1/30)*effectiveTilt b η^2 := by ring
      rw [heq]
      norm_num at hp ⊢
      exact hp
    · linarith only [hg]
  rw [centered_padded_cost_eq hb]
  have hf : 0 < 2*b*height b := by unfold height; positivity
  simpa only [mul_one] using mul_lt_mul_of_pos_left hcost hf

theorem centered_cubic_cost_strict {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      scaledCost b η (fun s => 1+η^2*(s^4+b^2*s^2)/2+c*η^3) < 2*b*height b := by
  have hh := centered_padding_strict hb (fun η => c*η/b^4)
    (by fun_prop) (by simp) (by
      filter_upwards [eventually_mem_nhdsWithin] with η hη
      have hηpos : 0 < η := hη
      positivity)
  filter_upwards [hh] with η hη
  have hb0 : b ≠ 0 := ne_of_gt hb
  have heq : (fun s : ℝ => 1+η^2*(s^4+b^2*s^2)/2+η^2*b^4*(c*η/b^4)) =
      (fun s => 1+η^2*(s^4+b^2*s^2)/2+c*η^3) := by
    funext s
    field_simp
  rwa [heq] at hη

theorem centered_fractional_cost_strict {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      scaledCost b η (fun s => 1+η^2*(s^4+b^2*s^2)/2+c*η^(5/2:ℝ)) < 2*b*height b := by
  have hh := centered_padding_strict hb (fun η => c*Real.sqrt η/b^4)
    (by fun_prop) (by simp) (Filter.Eventually.of_forall (fun η => by positivity))
  filter_upwards [hh, eventually_mem_nhdsWithin] with η hη hηpos
  have hb0 : b ≠ 0 := ne_of_gt hb
  have heq : (fun s : ℝ => 1+η^2*(s^4+b^2*s^2)/2+η^2*b^4*(c*Real.sqrt η/b^4)) =
      (fun s => 1+η^2*(s^4+b^2*s^2)/2+c*η^(5/2:ℝ)) := by
    funext s
    rw [RadialCaps.rpow_five_halves hηpos]
    field_simp
  rwa [heq] at hη

end RadialPhysical

end

end OAI

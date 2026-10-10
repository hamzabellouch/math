import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ExpectedTruncatedControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ContDiff

namespace CoulombAnalysis

lemma ball_translation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x : TFSpace => y+x) (ballMeasure R) (volume.restrict (ball y R)) := by
  have h := (measurePreserving_add_left (volume : Measure TFSpace) y).restrict_preimage
    (measurableSet_ball (x := y) (ε := R))
  have he : (fun x : TFSpace => y+x) ⁻¹' ball y R = ball 0 R := by
    ext x
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  simpa only [he,ballMeasure] using h

lemma setIntegral_translate_ball (y : TFSpace) (R : ℝ) (f : TFSpace → ℝ) :
    (∫ x in ball 0 R, f (y+x)) = ∫ x in ball y R, f x :=
  (ball_translation_preserving y R).integral_comp (MeasurableEquiv.addLeft y).measurableEmbedding f

lemma coulomb_short_range_holder_centered {R : ℝ} (hR : 0 < R) (y : TFSpace)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (volume.restrict (ball y R))) :
    (∫ x in ball y R, ‖f x‖/‖y-x‖) ≤
      (∫ x in ball y R, ‖f x‖^(5/3:ℝ))^(3/5:ℝ) *
      (8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ) := by
  have hh := coulomb_short_range_holder hR (hf.comp_measurePreserving (ball_translation_preserving y R))
  have he := setIntegral_translate_ball y R (fun x => ‖f x‖/‖y-x‖)
  simp only [sub_add_cancel_left,norm_neg] at he
  have hp := setIntegral_translate_ball y R (fun x => ‖f x‖^(5/3:ℝ))
  simp only [Function.comp_apply] at hh
  rw [he,hp] at hh
  exact hh

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem masterSmearing_potential_holder {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {ρ : Space → ℝ} (hmρ : Measurable ρ) (hρ : Integrable ρ) (hp : MemLp ρ (5/3))
    (hn : ∀ x, 0 ≤ ρ x) (y : Space) :
    |tfPotential ρ y-tfPotential (masterSmearing c₁ r₀ s g ρ) y| ≤
      (∫ x in ball y (2*masterWidth c₁ r₀ s y), ‖ρ x‖^(5/3:ℝ))^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*(2*masterWidth c₁ r₀ s y)^(1/5:ℝ) := by
  obtain ⟨h0,h1⟩ := masterSmearing_potential_loss hc hcL hr hs hs1 hg hcg hgn hrad hgs hmρ hρ hp hn y
  rw [abs_of_nonneg h0]
  have hh := coulomb_short_range_holder_centered
    (show 0 < 2*masterWidth c₁ r₀ s y by have hpos := masterWidth_pos hc hr hs y; positivity) y
    (hp.mono_measure Measure.restrict_le_self)
  calc
    _ ≤ ∫ x in ball y (2*masterWidth c₁ r₀ s y), ρ x/‖y-x‖ := h1
    _ = ∫ x in ball y (2*masterWidth c₁ r₀ s y), ‖ρ x‖/‖y-x‖ := by
      congr 1; funext x; rw [Real.norm_of_nonneg (hn x)]
    _ ≤ _ := hh

end CoulombAtom

end

end OAI

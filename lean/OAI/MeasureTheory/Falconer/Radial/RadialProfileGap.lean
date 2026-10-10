import OAI.MeasureTheory.Falconer.Radial.RadialProfileProduct

namespace OAI

/-! # The finite-depth error fits inside the strict weak radial profile gap -/

namespace Falconer

theorem eventually_radial_profile_gap (d J : ℕ) {e f β loss ℓ : ℝ}
    (hgap : (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)) < -ℓ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N ∧
      (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-
        (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ := by
  let margin := -ℓ-((J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)))
  have hm : 0 < margin := sub_pos.mpr hgap
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max 1 (β*(d:ℝ)*(J:ℝ)/margin))
  refine ⟨N₀,fun N hN => ?_⟩
  have hn : (1:ℝ) < N := (le_max_left _ _).trans_lt (hN₀.trans_le (by exact_mod_cast hN))
  have hn0 : 0 < N := by exact_mod_cast (zero_lt_one.trans hn)
  have hn' : (0:ℝ) < N := zero_lt_one.trans hn
  have hr : β*(d:ℝ)*(J:ℝ)/margin < (N:ℝ) :=
    (le_max_right _ _).trans_lt (hN₀.trans_le (by exact_mod_cast hN))
  have hb : β*(d:ℝ)*(J:ℝ)/(N:ℝ) < margin := by
    apply (div_lt_iff₀ hn').mpr
    have hh := (div_lt_iff₀ hm).mp hr
    nlinarith
  refine ⟨hn0,?_⟩
  have he : (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-
      (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) =
      ((J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)))+
        β*(d:ℝ)*(J:ℝ)/(N:ℝ) := by ring
  rw [he]
  dsimp [margin] at hb
  linarith

end Falconer

end OAI

import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceActualWord
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitude
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfiguration

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction HigherBiasSourceWord InitialCharacterScale Filter

theorem exists_actual_higher_character_sources (d : Decomposition) (α β mass δ : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hmass : 0 < mass) (hδ : 0 < δ) (hδu : δ ≤ 1) :
    ∃ ρ γ c₀ c BD0 : ℝ,0 < ρ ∧ 0 < γ ∧ 0 < c₀ ∧ 0 < c ∧ 1 ≤ BD0 ∧
      ∃ M h : ℕ,2 ≤ M ∧ ∃ Kmin : ℝ,0 < Kmin ∧
      ∀ BD : ℝ,BD0 ≤ BD → ∀ K0 : ℕ,Kmin ≤ (K0:ℝ) →
      ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,
        (∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        mass*L ≤ harmonicPrimeMass E → (∀ p∈E,δ ≤ higherPrimeBias d p) →
        ∃ j : Fin (h+1),∃ s : SelectedWordSource d E δ L (K0*M^j.val) α β ρ γ c₀,
          ∃ w : FixedConfigurationWitness s c BD,
          Real.exp (-amplitudeRate (selectionCost β (δ/2)) (configurationLossCoefficient β)*
            (wordSize (K0*M^j.val) L:ℝ)) ≤ ‖w.amplitude‖ := by
  classical
  obtain ⟨ρ,γ,c₀,hρ,hγ,hc₀,M,h,hM,Krich,hKrich,hsource⟩ :=
    exists_actual_selected_word_sources d α β mass δ hα hαβ hmass hδ
  obtain ⟨c,hc,Kcells,hfixed⟩ := exists_actual_fixed_configurations δ c₀ hδ hc₀
  obtain ⟨Kamp,hamp⟩ := eventually_atTop.mp
    (eventually_fixedConfiguration_amplitude d hα hαβ hρ hγ hc₀ hc hδ hδu)
  let BD0 := max 1 (gapThreshold (positiveRate (selectionCost β (δ/2))
    (configurationLossCoefficient β)) ρ (2*(β+1)) β)
  let Kmin := max Krich (max (Kcells:ℝ) (Kamp:ℝ))
  refine ⟨ρ,γ,c₀,c,BD0,hρ,hγ,hc₀,hc,le_max_left _ _,M,h,hM,Kmin,
    hKrich.trans_le (le_max_left _ _),?_⟩
  intro BD hBD K0 hK
  have hBD1 : 1 ≤ BD := (le_max_left _ _).trans hBD
  have hBDgap : gapThreshold (positiveRate (selectionCost β (δ/2))
      (configurationLossCoefficient β)) ρ (2*(β+1)) β ≤ BD := (le_max_right _ _).trans hBD
  have hKr : Krich ≤ (K0:ℝ) := (le_max_left _ _).trans hK
  have hKc : Kcells ≤ K0 := by
    exact_mod_cast ((le_max_left (Kcells:ℝ) (Kamp:ℝ)).trans ((le_max_right _ _).trans hK))
  have hKa : Kamp ≤ K0 := by
    exact_mod_cast ((le_max_right (Kcells:ℝ) (Kamp:ℝ)).trans ((le_max_right _ _).trans hK))
  have hkge (j : Fin (h+1)) : K0 ≤ K0*M^j.val :=
    Nat.le_mul_of_pos_right K0 (pow_pos (by omega : 0 < M) _)
  have hfixes := Filter.eventually_all.mpr (fun j : Fin (h+1) =>
    hfixed (K0*M^j.val) (hKc.trans (hkge j)) α β ρ γ BD hα hγ.le hBD1)
  have hampall := Filter.eventually_all.mpr (fun j : Fin (h+1) =>
    hamp (K0*M^j.val) (hKa.trans (hkge j)) BD hBDgap)
  filter_upwards [hsource K0 hKr,hfixes,hampall] with L hs hf ha
  intro E hE hEm hbias
  obtain ⟨j,⟨s⟩⟩ := hs E hE hEm hbias
  obtain ⟨cfg,H,_hbounded,hsub,hgeom,hgood,hpop⟩ := hf j d E s hE
  let w : FixedConfigurationWitness s c BD := ⟨cfg,H,hsub,hgeom,hgood,hpop⟩
  exact ⟨j,s,w,ha j E hE s w⟩

end Ostmann.Characters.HigherBiasSource

end

end OAI

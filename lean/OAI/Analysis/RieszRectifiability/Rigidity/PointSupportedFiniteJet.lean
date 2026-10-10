import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShrinkingSchwartzLocalization
import OAI.Analysis.RieszRectifiability.Rigidity.TemperedRealFiniteOrderBound
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzSupportLocalization
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalFourierAnnihilation

namespace OAI

/-!
# Finite jets of point-supported distributions

A finite Schwartz seminorm bound and shrinking localization show that a tempered distribution
supported at the origin annihilates tests whose derivatives vanish there through a fixed order.
Consequently it depends only on a finite jet. The final theorem applies this conclusion to the
inverse Fourier transform of a represented height distribution satisfying the fractional equation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap Filter Topology
open scoped FourierTransform

theorem point_supported_distribution_kills_zero_jets {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∀ g : 𝓢(Ambient d, ℂ),
      (∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = 0) → T g = 0 := by
  classical
  obtain ⟨s, C, hC, hbound⟩ := tempered_distribution_finite_real_seminorm_bound T
  let N : ℕ := s.sup Prod.snd
  refine ⟨N, fun g hz => ?_⟩
  let G : ℕ → 𝓢(Ambient d, ℂ) := shrinkingSchwartzCutoff g
  have hTG : ∀ j, T (G j) = T g := fun j =>
    tempered_distribution_eq_of_germ_at_zero T hT (G j) g (shrinkingSchwartzCutoff_germ g j)
  have hlim : ∀ i ∈ s, Tendsto
      (fun j => schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j)) atTop (𝓝 0) := by
    intro i hi
    have hn : i.2 ≤ N := Finset.le_sup hi
    exact shrinkingSchwartzCutoff_seminorm_tendsto g i.1 i.2
      (fun k hk => hz k (hk.trans hn))
  have hsum : Tendsto (fun j => C * ∑ i ∈ s,
      schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using!
      (tendsto_finsetSum s hlim).const_mul C
  have hle : ∀ j, ‖T g‖ ≤ C * ∑ i ∈ s,
      schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j) := by
    intro j
    rw [← hTG j]
    apply (hbound (G j)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hs := Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ (Ambient d) ℂ) s (G j)
    simpa only [← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply] using! hs
  have hzero : ‖T g‖ ≤ 0 := ge_of_tendsto hsum (Eventually.of_forall hle)
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

theorem point_supported_distribution_finite_jet {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∀ g h : 𝓢(Ambient d, ℂ),
      (∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i h 0) → T g = T h := by
  obtain ⟨N, hN⟩ := point_supported_distribution_kills_zero_jets T hT
  refine ⟨N, fun g h heq => ?_⟩
  have hz : ∀ i, i ≤ N → iteratedFDeriv ℝ i (g - h) 0 = 0 := by
    intro i hi
    change iteratedFDeriv ℝ i ((g : Ambient d → ℂ) - (h : Ambient d → ℂ)) 0 = 0
    rw [iteratedFDeriv_sub_apply (g.contDiffAt i) (h.contDiffAt i), heq i hi, sub_self]
  have hh := hN (g - h) hz
  rw [map_sub, sub_eq_zero] at hh
  exact hh

theorem represented_height_inverse_fourier_finite_jet (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ N : ℕ, ∀ g h : 𝓢(Ambient (p + 1), ℂ),
      (∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i h 0) →
      (𝓕⁻ T : 𝓢'(Ambient (p + 1), ℂ)) g = (𝓕⁻ T : 𝓢'(Ambient (p + 1), ℂ)) h := by
  apply point_supported_distribution_finite_jet
  intro g hc hz
  exact represented_height_inverse_fourier_annihilates_away_zero p w T hT heq g hc hz

end

end RieszRectifiability

end OAI

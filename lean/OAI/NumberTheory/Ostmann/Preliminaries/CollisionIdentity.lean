import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMass
import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem collision_stability_identity {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (μ ν : ZMod p → ℝ) (hμ : ∑ x, μ x = 1) (hν : ∑ x, ν x = 1)
    (hμS : ∀ x ∉ S, μ x = 0) (hνSc : ∀ x ∉ Sᶜ, ν x = 0) :
    uniformDefect S μ + uniformDefect Sᶜ ν +
        (((S.card : ℝ) / p)⁻¹ + (1 - (S.card : ℝ) / p)⁻¹ - 4) / p =
      massEnergy μ + massEnergy ν - 4 / p := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hspos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have htpos : (0 : ℝ) < Sᶜ.card := by exact_mod_cast hSc.card_pos
  have hcard : (S.card : ℝ) + Sᶜ.card = p := by
    exact_mod_cast (Finset.card_add_card_compl S).trans (ZMod.card p)
  have hcomp : 1 - (S.card : ℝ) / p = (Sᶜ.card : ℝ) / p := by
    apply (eq_div_iff (ne_of_gt hpos)).mpr
    field_simp
    linarith
  rw [uniformDefect_eq_energy_sub S hS μ hμ hμS,
    uniformDefect_eq_energy_sub Sᶜ hSc ν hν hνSc, hcomp]
  field_simp
  ring

theorem collision_stability_terms_nonneg {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (μ ν : ZMod p → ℝ) :
    0 ≤ uniformDefect S μ ∧ 0 ≤ uniformDefect Sᶜ ν ∧
      0 ≤ (((S.card : ℝ) / p)⁻¹ + (1 - (S.card : ℝ) / p)⁻¹ - 4) / p := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hspos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have htpos : (0 : ℝ) < Sᶜ.card := by exact_mod_cast hSc.card_pos
  have hcard : (S.card : ℝ) + Sᶜ.card = p := by
    exact_mod_cast (Finset.card_add_card_compl S).trans (ZMod.card p)
  refine ⟨uniformDefect_nonneg S μ, uniformDefect_nonneg Sᶜ ν, ?_⟩
  exact div_nonneg (reciprocal_density_penalty_nonneg (div_pos hspos hpos)
    ((div_lt_one hpos).mpr (by linarith))) hpos.le

theorem decomposition_collision_identity (d : Decomposition) (p : ℕ) [NeZero p]
    (hp : p.Prime) (μ ν : ZMod p → ℝ)
    (hμ : ∑ x, μ x = 1) (hν : ∑ x, ν x = 1)
    (hμS : ∀ x ∉ d.residueSupport p, μ x = 0)
    (hνSc : ∀ x ∉ (d.residueSupport p)ᶜ, ν x = 0) :
    uniformDefect (d.residueSupport p) μ + uniformDefect (d.residueSupport p)ᶜ ν +
        ((d.residueDensity p)⁻¹ + (1 - d.residueDensity p)⁻¹ - 4) / p =
      massEnergy μ + massEnergy ν - 4 / p :=
  collision_stability_identity (d.residueSupport p) (d.residueSupport_nonempty p)
    (d.residueSupport_compl_nonempty p hp) μ ν hμ hν hμS hνSc

end Ostmann.Preliminaries

end OAI

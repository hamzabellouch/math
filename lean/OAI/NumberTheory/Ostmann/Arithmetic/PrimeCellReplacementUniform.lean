import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression

theorem exists_primeCell_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi-lo ≤ 1 → ∀ (N M : ℕ) [NeZero M] (Z : ℝ),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < Z →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1/3 : ℝ)) →
      (∀ a : ZMod M, IsUnit a →
        |residueMass N M a lo hi Z - harmonicIntegral M lo hi / Z| ≤
          (K/Z) * Real.exp (-d * lo ^ (1/3 : ℝ))) ∧
      (∀ F : (ZMod M)ˣ → ℝ, (∀ u, 0 ≤ F u) →
        |realTestSum N M lo hi Z F -
          (harmonicIntegral M lo hi / Z) * ∑ u : (ZMod M)ˣ, F u| ≤
          ((K/Z) * Real.exp (-d * lo ^ (1/3 : ℝ))) * ∑ u : (ZMod M)ˣ, F u) ∧
      (∀ F : (ZMod M)ˣ → ℂ,
        ‖complexTestSum N M lo hi Z F -
          ((harmonicIntegral M lo hi / Z : ℝ) : ℂ) * ∑ u : (ZMod M)ˣ, F u‖ ≤
          ((K/Z) * Real.exp (-d * lo ^ (1/3 : ℝ))) * ∑ u : (ZMod M)ˣ, ‖F u‖) := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,h⟩ := exists_residueMass_error_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi hlo hlohi hlen N M _ Z hN hZ hmod
  have hmass (u : (ZMod M)ˣ) :
      |residueMass N M u lo hi Z - harmonicIntegral M lo hi / Z| ≤
        (K/Z) * Real.exp (-d * lo ^ (1/3 : ℝ)) :=
    h lo hi hlo hlohi hlen N M u Z hN (NeZero.pos M) u.isUnit hZ hmod
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact h lo hi hlo hlohi hlen N M a Z hN (NeZero.pos M) ha hZ hmod
  · intro F hF
    exact realTestSum_error N M lo hi Z _ _ F hF hmass
  · intro F
    exact complexTestSum_error N M lo hi Z _ _ F hmass

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI

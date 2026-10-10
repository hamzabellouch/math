import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitFormula
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimePowerSupplyDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyErrorAssembly

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

theorem eventually_totalPrimitiveError_supply {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      totalPrimitiveError Q none φ (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  obtain ⟨C,hC,hformula⟩ := Ostmann.Dirichlet.exists_smoothed_explicit_formula φ hφ hcompact 8
  apply eventually_totalPrimitiveError_of_truncated_formula hφ hcompact hs 7 hC ?_ D
  intro Q χ X T hX hT
  have hh := hformula (χ.val.1.val+1) χ.val.2.val χ.property X T hX hT
  simpa only [Ostmann.Dirichlet.upperZeroWeight,contourRemainder,Nat.cast_add,
    Nat.cast_one,add_assoc,show (7+1 : ℕ)=8 by norm_num] using hh

theorem eventually_totalPrimitivePrimeError_supply {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      Ostmann.Supply.totalPrimitivePrimeError Q none φ (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) :=
  prime_error_supply_decay_of_vonMangoldt hφ.continuous hs
    (eventually_totalPrimitiveError_supply hφ hcompact hs) D

end Ostmann.ZeroDensity

end

end OAI

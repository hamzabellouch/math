import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorActual
import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorSelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction Filter

theorem eventually_exists_actual_mixed_spectator_facade (d : Decomposition)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,∃ (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
      (hZ : 0 < harmonicPrimeMass P),
      P=mixedSpectatorPrimes d δ L ∧ L/5000 ≤ harmonicPrimeMass P ∧
      (L/5000)*Real.exp (Real.exp ((1/2000:ℝ)*L)) ≤ (P.card:ℝ) ∧
      (∀p∈P,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℝ) ∧
        Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) ∧
      (1/2:ℝ) ≤ (harmonicPrimeSource P hP hZ).law.mean (fun p=>balancedPrimeIndicator d p) ∧
      (∀p∈P,Supply.balancedDensity d p ∧ mixedPrimeBias d p < δ) :=
  eventually_exists_actual_mixed_spectator d δ hδ

end Ostmann.Characters

end

end OAI

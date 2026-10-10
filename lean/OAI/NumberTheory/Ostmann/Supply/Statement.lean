import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open Filter

def residueGamma (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p = 0 then 0 else
    letI : NeZero p := ⟨hp⟩
    gamma (d.residueSupport p)

theorem residueGamma_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    residueGamma d p = gamma (d.residueSupport p) := by
  simp [residueGamma, NeZero.ne p]

def residueDensityTotal (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p = 0 then 0 else
    letI : NeZero p := ⟨hp⟩
    d.residueDensity p

theorem residueDensityTotal_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    residueDensityTotal d p = density (d.residueSupport p) := by
  simp [residueDensityTotal, NeZero.ne p, density, Decomposition.residueDensity]

def nonsparsePrimes (d : Decomposition) (δ L : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (Real.exp ((9/10:ℝ)*L))⌋₊ + 1)).filter (fun p =>
    p.Prime ∧ (1/20:ℝ)*L ≤ Real.log (Real.log p) ∧
      Real.log (Real.log p) ≤ (9/10:ℝ)*L ∧
      (1/3:ℝ) ≤ residueDensityTotal d p ∧ residueDensityTotal d p ≤ (2/3:ℝ) ∧
      δ ≤ residueGamma d p)

def NonsparseSupply : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ d : Decomposition, ∀ᶠ L : ℝ in atTop,
    (3/20:ℝ)*L ≤ ∑ p ∈ nonsparsePrimes d δ L, (1:ℝ)/p

end Ostmann.Supply

end

end OAI

import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScaleCutoff
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScaleUniform
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTypicalMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Ostmann.Preliminaries Ostmann.Construction Filter
open scoped BigOperators

theorem eventually_higherSourceTypical_at_scale (d : Decomposition) (δ c₀ : ℝ)
    (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    ∃ cA : ℝ,0 < cA ∧ ∀ (k N : ℕ) (α β : ℝ),0 < α →
      ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      let X := higherSourceX k u
      ∀ (ι : Type) [Fintype ι],Fintype.card ι ≤ N →
      ∀ E : Finset (PrimeUpTo (collisionScale 10 X)),
      ∀ F : HigherBiasSourceFamily d (collisionScale 10 X) E δ,
      ∀ G : ι → Finset (PrimeUpTo (collisionScale 10 X)),
      (∀ i,G i ⊆ E) → ∀ hm : ∀ i,0 < primeShellMass (G i),
      (∀ i,c₀ ≤ primeShellMass (G i)) →
      (∀ i,∀ p∈G i,Real.exp (α*L) ≤ Real.log p.val) →
      ∃ H : Finset ℕ,H ⊆ upperWindow d.A X ∧
        cA*Real.sqrt X/(Real.log (X:ℝ))^3 ≤ H.card ∧
        ∀ a∈H,∀ i,δ/2 ≤
          ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (a:ZMod p.val))).re := by
  obtain ⟨cA,hcA,htyp⟩ := eventually_higherSourceTypical_mass d δ c₀ hδ hc₀
  refine ⟨cA,hcA,?_⟩
  intro k N α β hα
  filter_upwards [eventually_higherSourceX_property k α hα htyp,
    eventually_higherSource_testCount_le k α hα N,
    eventually_higherSource_loglog_sq_le_prime_log k α β hα 1 (by norm_num)]
    with L htyp hcount hscale
  intro u hul huu
  dsimp only
  intro ι _ hι E F G hG hm hmass hprimes
  have hN := hcount u hul
  apply htyp u hul ι ((Nat.cast_le.mpr hι).trans hN) E F G hG hm hmass
  intro i p hp
  simpa only [one_mul] using hscale u hul huu p.val (hprimes i p hp)

end Ostmann.Characters

end

end OAI

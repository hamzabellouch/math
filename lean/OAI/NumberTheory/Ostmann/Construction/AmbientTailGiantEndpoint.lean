import OAI.NumberTheory.Ostmann.Construction.SmoothGiantAmbientPrior
import OAI.NumberTheory.Ostmann.Construction.TailGiantEndpointStatistic

namespace OAI

/-! # The selected giant supplies its endpoint mean in the common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem ambient_tail_giant_endpoint_lower
    (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (G δ : ℝ) (hsub : smoothGiantPrimeRange G ⊆ P) (hE : E.Nonempty)
    (hmean : δ ≤ ∑ q : smoothGiantPrimeRange G,
      smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G q * tailGiantEndpointMean A N F E q) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    ((E.image fun a : ℕ => (a : ℤ)).card : ℝ) * δ ≤
      ∑ a ∈ E.image (fun a : ℕ => (a : ℤ)),
        (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
          primePhysicalTest (tailDensityMask A N p) true (decide ((p : ℕ) ∈ F))
            (a : ZMod (p : ℕ))).re := by
  intro
  apply tailGiantEndpointMean_endpoint_lower A N F E P hP
    (smoothGiantPrior P logCellProfile G) δ hE
  have he := smoothGiantPrior_ambient_mean P hP logCellProfile G logCellProfile_zero_outside
    hsub (fun p => tailGiantEndpointMean A N F E p)
  exact hmean.trans_eq he.symm

end Ostmann

end OAI

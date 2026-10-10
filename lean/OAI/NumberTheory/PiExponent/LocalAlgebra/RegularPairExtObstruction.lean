import Mathlib.RingTheory.Finiteness.Prod
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer
import OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight
import OAI.NumberTheory.PiExponent.LocalAlgebra.PairResolutionShortComplex

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentJets.PolynomialLocalUnmixedness

variable {S : Type u} [CommRing S]

theorem regular_pair_ext_zero (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) (X : ModuleCat.{u} S)
    (h₀ : Subsingleton (Ext X (ModuleCat.of S S) 0))
    (h₁ : Subsingleton (Ext X (ModuleCat.of S S) 1))
    (h₂ : Subsingleton (Ext X (ModuleCat.of S S) 2)) :
    Subsingleton (Ext X (ModuleCat.of S (S ⧸ Ideal.ofList [f, g])) 0) := by
  exact lengthTwo_ext_zero X (pairQuotientShortComplex f g)
    (pairSyzygyShortComplex f g) (pairQuotientShortComplex_shortExact f g)
    (pairSyzygyShortComplex_shortExact f g hreg)
    (pair_resolution_shortComplex_link f g) h₀
    (PiExponentSiegelAux.W31.ext_subsingleton_of_finite_free (F := S × S) X 1 h₁) h₂

theorem regular_pair_associatedPrime_ext_obstruction [IsNoetherianRing S]
    (f g : S) (hreg : RingTheory.Sequence.IsRegular S [f, g])
    (P : Ideal S) (hP : IsAssociatedPrime P (S ⧸ Ideal.ofList [f, g])) :
    ∃ i : ℕ, i ≤ 2 ∧
      ¬ Subsingleton (Ext (ModuleCat.of S (S ⧸ P)) (ModuleCat.of S S) i) := by
  classical
  by_contra h
  have hv (i : ℕ) (hi : i ≤ 2) :
      Subsingleton (Ext (ModuleCat.of S (S ⧸ P)) (ModuleCat.of S S) i) := by
    by_contra hv
    exact h ⟨i, hi, hv⟩
  have he := regular_pair_ext_zero f g hreg (ModuleCat.of S (S ⧸ P))
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide))
  exact not_isAssociatedPrime_of_ext_zero P he hP

end PiExponentJets.W18

end

end OAI

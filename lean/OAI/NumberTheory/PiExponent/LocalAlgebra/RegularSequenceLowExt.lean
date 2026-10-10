import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R]

theorem regularSequenceQuotientExt_positive_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) :=
  W31.regularSequenceQuotientExt_of_dual_exact rs hreg n
    (regularSequenceComplex_dual_low_exact rs hreg n hn)

theorem regularSequenceQuotientExt_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) 0) := by
  let := regularSequenceQuotient_dual_subsingleton rs hreg hne
  refine ⟨fun a b => Ext.homEquiv₀.injective ?_⟩
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

theorem regularSequenceQuotientExt_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) n) := by
  cases n with
  | zero =>
    apply regularSequenceQuotientExt_zero rs hreg
    intro h
    simp [h] at hn
  | succ n => exact regularSequenceQuotientExt_positive_below_length rs hreg n hn

theorem residueFieldExt_below_regular_length [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of R R) n) := by
  change Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R R) n)
  rw [← hmax]
  exact regularSequenceQuotientExt_below_length rs hreg n hn

end PiExponentSiegelAux.W30

end

end OAI

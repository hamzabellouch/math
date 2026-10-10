import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Localization
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

lemma residueCoordinate_aeval (f : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval (residueCoordinate K n Q) f =
      algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) f := by
  have he : MvPolynomial.aeval (residueCoordinate K n Q) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) := by
    ext i
    simp only [MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun he f

theorem residueCoordinate_adjoin_top :
    IntermediateField.adjoin K (Set.range (residueCoordinate K n Q)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, hb, hz⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin n) K ⧸ Q) z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (IntermediateField.mem_adjoin_range_iff K (residueCoordinate K n Q) z).mpr
  refine ⟨f, g, ?_⟩
  simpa only [residueCoordinate_aeval,
    Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem exists_coordinate_residue_basis :
    ∃ t : Set (LocalPolynomialResidue K n Q),
      t.Finite ∧ t ⊆ Set.range (residueCoordinate K n Q) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  have htop := residueCoordinate_adjoin_top K n Q
  let : Algebra.IsAlgebraic
      (Algebra.adjoin K (Set.range (residueCoordinate K n Q)))
      (LocalPolynomialResidue K n Q) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, ht, htb⟩ :=
    exists_isTranscendenceBasis_subset (R := K) (Set.range (residueCoordinate K n Q))
  exact ⟨t, (Set.finite_range _).subset ht, ht, htb⟩

theorem exists_coordinate_basis_indices :
    ∃ (t : Set (LocalPolynomialResidue K n Q)) (j : t → Fin n),
      t.Finite ∧ Function.Injective j ∧
      (∀ a, residueCoordinate K n Q (j a) = (a : LocalPolynomialResidue K n Q)) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  classical
  obtain ⟨t, hfin, ht, htb⟩ := exists_coordinate_residue_basis K n Q
  choose j hj using fun a : t => ht a.property
  refine ⟨t, j, hfin, ?_, hj, htb⟩
  intro a b hab
  apply Subtype.ext
  exact (hj a).symm.trans ((congrArg (residueCoordinate K n Q) hab).trans (hj b))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI

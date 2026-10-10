import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelativeSemisimpleCorrection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingSemisimpleFixedRepresentative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearConjugationCentralizer

namespace OAI

/-! # Successive semisimple corrections preserve all earlier centralizers -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_centralizer_correction_preserving_family
    (A S U B : L ≃ₗ⁅ℝ⁆ L) (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (hTS : ∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap)
    (hTU : ∀ T ∈ ss, Commute T.toLinearMap U.toLinearMap)
    (hTB : ∀ T ∈ ss, Commute T.toLinearMap B.toLinearMap)
    (u : L) (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap) :
    ∃ v : L, (∀ T ∈ ss, T v = v) ∧
      Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  have hTA (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap A.toLinearMap := by
    rw [hA]
    exact (hTS T ht).mul_right (hTU T ht)
  have hTi (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) :
      Commute T.toLinearMap (polynomialInnerLieEquiv u).toLinearMap := by
    apply linear_commute_of_mul_equiv_right _ _ A.toLinearEquiv (hTA T ht)
    change Commute T.toLinearMap
      ((polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap)
    rw [hu]
    exact linear_commute_conj B.toLinearEquiv T.toLinearMap A.toLinearMap (hTB T ht) (hTA T ht)
  obtain ⟨w, hw, hiw, _⟩ := commuting_semisimple_inner_fixed_representative ss hss hpair u hTi
  have huw : (polynomialInnerLieEquiv w).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap := by rw [hiw]; exact hu
  let I := {T : L ≃ₗ⁅ℝ⁆ L // T ∈ ss}
  obtain ⟨v, hv, hc⟩ := semisimple_centralizer_inner_correction_fixed A S U B
    (fun t : I => t.val) hS hU hSU hA
    (fun t => hTS t.val t.property) (fun t => hTU t.val t.property) w
    (fun t => hw t.val t.property) huw
  exact ⟨v, fun T ht => hv ⟨T, ht⟩, hc⟩

/-- The next Jordan factor can be chosen in the common commutant. Corrections
of every further outer-centralizing element preserve the whole earlier family. -/
theorem exists_semisimple_factor_with_preserving_corrections
    (A : L ≃ₗ⁅ℝ⁆ L) (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (hTA : ∀ T ∈ ss, Commute T.toLinearMap A.toLinearMap) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      A.toLinearMap = S.toLinearMap * U.toLinearMap ∧
      (∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap) ∧
      ∀ B : L ≃ₗ⁅ℝ⁆ L, (∀ T ∈ ss, Commute T.toLinearMap B.toLinearMap) →
        ∀ u : L, (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
          B.toLinearEquiv.conjRingEquiv A.toLinearMap →
          ∃ v : L, (∀ T ∈ ss, T v = v) ∧
            Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  obtain ⟨S, U, hS, hU, hSU, hA, hcentral⟩ := real_lie_jordan_decomposition_centralizer A
  have hTS (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap S.toLinearMap :=
    (hcentral T.toLinearMap (hTA T ht).symm).1.symm
  have hTU (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap U.toLinearMap :=
    (hcentral T.toLinearMap (hTA T ht).symm).2.symm
  exact ⟨S, U, hS, hU, hSU, hA, hTS, fun B hTB u hu =>
    semisimple_centralizer_correction_preserving_family A S U B ss
      hS hU hSU hA hss hpair hTS hTU hTB u hu⟩

end PolycyclicRecognition

end

end OAI

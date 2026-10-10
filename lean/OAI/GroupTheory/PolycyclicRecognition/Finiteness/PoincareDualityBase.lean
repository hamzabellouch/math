import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteDimensionTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupFiniteGenerationFromFP
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Abelian

namespace OAI

/-! # The dimension-zero and abelian cases of the solvable duality endgame -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem leftRegular_invariants_eq_zero_of_infinite [Infinite G] (x : ℤ[G])
    (hx : ∀ g, Representation.leftRegular ℤ G g x = x) : x = 0 := by
  classical
  obtain ⟨a, ha⟩ := x.coeff.support.exists_notMem
  have ha0 : x.coeff a = 0 := Finsupp.notMem_support_iff.mp ha
  ext b
  have he := congrArg (fun y : ℤ[G] => y.coeff b) (hx (b * a⁻¹))
  have hab : x.coeff a = x.coeff b := by
    simpa [Representation.leftRegular, Representation.coeff_ofMulAction, mul_assoc] using he
  exact hab.symm.trans ha0

theorem regular_cohomology_zero_of_infinite [Infinite G] :
    IsZero (groupCohomology (Rep.leftRegular ℤ G) 0) := by
  apply IsZero.of_iso (Y := ModuleCat.of ℤ (Representation.leftRegular ℤ G).invariants)
    _ (groupCohomology.H0Iso _)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (x : (Representation.leftRegular ℤ G).invariants) : x = 0 := by
    apply Subtype.ext
    exact leftRegular_invariants_eq_zero_of_infinite (G := G) x.val x.property
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem IsIntegralPoincareDualityGroup.subsingleton_of_zero
    (hG : IsIntegralPoincareDualityGroup G 0) : Subsingleton G := by
  have hfinite : Finite G := by
    cases finite_or_infinite G with
    | inl h => exact h
    | inr h =>
      let := h
      obtain ⟨e⟩ := hG.2.2
      have hz : IsZero (ModuleCat.of ℤ ℤ) :=
        IsZero.of_iso regular_cohomology_zero_of_infinite e.symm
      have h01 : (0 : ℤ) = 1 := ModuleCat.isZero_iff_subsingleton.mp hz |>.elim _ _
      exact (zero_ne_one h01).elim
  let := hfinite
  exact subsingleton_of_finite_torsionFree G hG.torsionFree

theorem IsIntegralPoincareDualityGroup.polycyclic_of_zero
    (hG : IsIntegralPoincareDualityGroup G 0) : IsPolycyclic G := by
  let := hG.subsingleton_of_zero
  exact isPolycyclic_of_subsingleton

section Abelian
variable {A : Type} [CommGroup A]

theorem IsIntegralPoincareDualityGroup.polycyclic_of_commGroup {n : ℕ}
    (hA : IsIntegralPoincareDualityGroup A n) : IsPolycyclic A := by
  let : Group.FG A := (hA.typeFPInfinity A 1).fg
  exact isPolycyclic_of_finitelyGenerated_commGroup A

end Abelian
end PolycyclicRecognition

end

end OAI

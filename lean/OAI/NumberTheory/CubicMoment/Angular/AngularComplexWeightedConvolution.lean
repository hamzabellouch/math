import OAI.NumberTheory.CubicMoment.Angular.AngularArithmeticTwist
import OAI.NumberTheory.CubicMoment.Angular.AngularShortUnsplitTuple
import OAI.NumberTheory.CubicMoment.Estimates.ComplexWeightedConvolution

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

/-- Independent residue characters and Mellin heights remain attached to
individual factors after exact collection. -/
theorem angularTwistedProductPolynomial_eq_unsplit (A : ι → EisensteinArithmeticFunction)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hη : ∀ i, AngularUnitCompatible (q i) (η i) ℓ)
    (t : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i))
      (mixedCubic a b) V Y = primaryAngularUnsplitTuple ℓ A a b q η t V Y := by
  rw [primaryComplexProductPolynomial_eq_tuple _ _ V hY hV]
  unfold primaryAngularUnsplitTuple
  apply Finset.sum_congr rfl
  intro n hn
  have hp (i : ι) : primary (n i) :=
    (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1
  simp_rw [angularTwistArithmetic_coeff_primary ℓ _ _ (hη _) _ _ (hp _)]
  rw [mixedCubic_prod _ _ ha hb]
  unfold primaryAngularTupleCore
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end CubicFirstMoment

end

end OAI

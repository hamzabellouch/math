import OAI.NumberTheory.CubicMoment.Angular.AngularSmoothShortContinuity

namespace OAI

/-! Full Mellin separation of the angular short tuple. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryAngularShortTupleSum_integral (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryAngularShortTupleSum ℓ X A a b q η W t V Z =
      ∫ τ : ℝ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  rw [primaryAngularShortTupleSum_mellin ℓ X A a b q η W t hX hW V hV hpos hsm hZ,
    ← integral_const_mul]
  congr 1
  funext τ
  unfold zeroLineMellinWeight
  ring

end CubicFirstMoment

end

end OAI

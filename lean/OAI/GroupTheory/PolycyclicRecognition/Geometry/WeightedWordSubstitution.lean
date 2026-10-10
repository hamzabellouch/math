import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousUniversalLogarithm

namespace OAI

/-! # Substitution in a nilpotent associative algebra -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

def weightedWordSubstitution : TruncatedWords c n →ₗ[ℚ] A :=
  (Finsupp.lsum ℚ (fun w : FreeMonoid (Fin n) =>
    (truncatedScalarCoefficient c w.length).smulRight (FreeMonoid.lift X w))).comp
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem weightedWordSubstitution_single (w : FreeMonoid (Fin n))
    (a : TruncatedRationalScalars c) :
    weightedWordSubstitution X (MonoidAlgebra.single w a) =
      truncatedScalarCoefficient c w.length a • FreeMonoid.lift X w := by
  change Finsupp.lsum ℚ _ (Finsupp.single w a) = _
  rw [Finsupp.lsum_single]
  rfl

theorem weightedWordSubstitution_weightedWord
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    (w : FreeMonoid (Fin n)) :
    weightedWordSubstitution X (weightedWord c n w) = FreeMonoid.lift X w := by
  rw [weightedWord, weightedWordSubstitution_single]
  by_cases hw : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length w.length hw]
    simp
  · rw [hX w (Nat.lt_of_not_ge hw), smul_zero]

theorem weightedWordSubstitution_mul
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    {p q : TruncatedWords c n} (hp : p ∈ weightedWordSpan c n) (hq : q ∈ weightedWordSpan c n) :
    weightedWordSubstitution X (p * q) =
      weightedWordSubstitution X p * weightedWordSubstitution X q := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨v, rfl⟩ := hq
      rw [← weightedWord_mul, weightedWordSubstitution_weightedWord X hX,
        weightedWordSubstitution_weightedWord X hX, weightedWordSubstitution_weightedWord X hX,
        map_mul]
    | zero => simp
    | add q r _ _ hq hr => simp only [mul_add, map_add, hq, hr]
    | smul a q _ hq => simp only [Algebra.mul_smul_comm, map_smul, hq]
  | zero => simp
  | add p r _ _ hp hr => simp only [add_mul, map_add, hp, hr]
  | smul a p _ hp => simp only [smul_mul_assoc, map_smul, hp]

theorem weightedWordSubstitution_one
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0) :
    weightedWordSubstitution X (1 : TruncatedWords c n) = 1 := by
  rw [← weightedWord_one c n, weightedWordSubstitution_weightedWord X hX, map_one]

def weightedWordSubstitutionHom
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0) :
    weightedWordSubalgebra c n →ₐ[ℚ] A :=
  AlgHom.ofLinearMap
    ((weightedWordSubstitution X).comp (weightedWordSubalgebra c n).toSubmodule.subtype)
    (weightedWordSubstitution_one X hX)
    (fun p q => weightedWordSubstitution_mul (c := c) (n := n) X hX p.2 q.2)

end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BilinearGeneratorOrbit

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def polynomialListProduct (m : V → V → V) : List V → V
  | [] => 0
  | x :: xs => m x (polynomialListProduct m xs)

theorem exp_polynomialListProduct (m : V → V → V) (h : PolynomialGroupLaws m)
    (xs : List V) :
    PolynomialCoordinateGroup.exp m h (polynomialListProduct m xs) =
      (xs.map (PolynomialCoordinateGroup.exp m h)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change PolynomialCoordinateGroup.exp m h (m x (polynomialListProduct m xs)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih]
    rfl

theorem contDiff_polynomialWord {c : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → I → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) (w : List (I × ℝ)) :
    ContDiff ℝ k (fun p => polynomialWord (dynkinProduct a (B p)) (X p) w) := by
  induction w with
  | nil => exact contDiff_const
  | cons z w ih =>
    rcases z with ⟨i, t⟩
    exact contDiff_dynkinProduct a B _ _ hB ((hX i).const_smul t) ih

theorem contDiff_polynomialListProduct_ofFn {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => polynomialListProduct (dynkinProduct a (B p)) (List.ofFn (X p))) := by
  induction n with
  | zero => simpa [List.ofFn_zero, polynomialListProduct] using
      (contDiff_const : ContDiff ℝ k (fun _ : P => (0 : V)))
  | succ n ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact contDiff_dynkinProduct a B _ _ hB (hX 0)
      (ih (fun p i => X p i.succ) (fun i => hX i.succ))

/-- The expanded conjugate scheme, evaluated as a polynomial in every
parameter, whether or not that parameter defines a group law. -/
def polynomialEndpointScheme {c n : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (p : (V →L[ℝ] V →L[ℝ] V) × (I → V)) (t : Fin n → ℝ) : V :=
  polynomialListProduct (dynkinProduct a p.1) (List.ofFn (fun k =>
    dynkinProduct a p.1
      (dynkinProduct a p.1 (polynomialWord (dynkinProduct a p.1) p.2 (w k))
        (t k • p.2 (i k)))
      (polynomialWord (dynkinProduct a p.1) p.2 (inverseGeneratorWord (w k)))))

variable [Fintype I]

/-- Joint smoothness includes the law and generator data, rather than just
the inserted amplitudes at one fixed law. -/
theorem contDiff_polynomialEndpointScheme {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (w : Fin n → List (I × ℝ)) (i : Fin n → I) :
    ContDiff ℝ k (fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin n → ℝ) =>
      polynomialEndpointScheme a w i z.1 z.2) := by
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    apply contDiff_dynkinProduct
    · exact contDiff_fst.fst
    · apply contDiff_dynkinProduct
      · exact contDiff_fst.fst
      · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
          (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (w j)
      · exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).smul
          ((contDiff_apply ℝ V (i j)).comp contDiff_fst.snd)
    · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
        (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (inverseGeneratorWord (w j))

end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.AmplitudeWordCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateSchemeBasis

namespace OAI

/-! # The conjugate scheme inside a word with independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

variable {I : Type*} {n d c : ℕ}

/-- Each slot remembers either a fixed amplitude or one inserted coordinate. -/
def schemeAmplitudeSlots (w : Fin n → List (I × ℝ)) (i : Fin n → I) :
    List (I × (ℝ ⊕ Fin n)) :=
  (List.ofFn fun j =>
    (w j).map (fun p => (p.1, Sum.inl p.2)) ++ [(i j, Sum.inr j)] ++
      (inverseGeneratorWord (w j)).map (fun p => (p.1, Sum.inl p.2))).flatten

def evaluateAmplitudeSlot (t : Fin n → ℝ) : ℝ ⊕ Fin n → ℝ :=
  Sum.elim id t

theorem map_schemeAmplitudeSlots (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (schemeAmplitudeSlots w i).map (fun p => (p.1, evaluateAmplitudeSlot t p.2)) =
      generatorSchemeWord w i t := by
  simp [schemeAmplitudeSlots, generatorSchemeWord, List.map_flatten,
    List.map_map, List.map_ofFn, evaluateAmplitudeSlot, Function.comp_def]

/-- All amplitudes of the expanded word are smooth affine functions of the
original inserted coordinates. -/
theorem contDiff_evaluateAmplitudeSlots (l : List (I × (ℝ ⊕ Fin n))) {q : ℕ∞} :
    ContDiff ℝ q (fun t : Fin n → ℝ => fun j : Fin l.length =>
      evaluateAmplitudeSlot t (l.get j).2) := by
  apply contDiff_pi.mpr
  intro j
  cases (l.get j).2 with
  | inl r => exact contDiff_const
  | inr k => exact contDiff_apply ℝ ℝ k

theorem polynomialWord_eq_listProduct {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (m : V → V → V) (X : I → V) (l : List (I × ℝ)) :
    polynomialWord m X l =
      polynomialListProduct m (l.map (fun p => p.2 • X p.1)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨i, t⟩
    simpa only [polynomialWord, List.map_cons, polynomialListProduct] using congrArg (m (t • X i)) ih

/-- Flattening the slots preserves the genuine endpoint at every group law. -/
theorem amplitudeWord_scheme_eq (a : DynkinCoefficients c 2)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (X : I → Fin d → ℝ) (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    amplitudeWordEndpoint a (fun j => ((schemeAmplitudeSlots w i).get j).1) (B, X)
      (fun j => evaluateAmplitudeSlot t ((schemeAmplitudeSlots w i).get j).2) =
        polynomialEndpointScheme a w i (B, X) t := by
  let l := schemeAmplitudeSlots w i
  have he : (List.ofFn fun j : Fin l.length =>
      ((l.get j).1, evaluateAmplitudeSlot t (l.get j).2)) = generatorSchemeWord w i t := by
    change List.ofFn ((fun p => (p.1, evaluateAmplitudeSlot t p.2)) ∘ l.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
    exact map_schemeAmplitudeSlots w i t
  have hw : amplitudeWordEndpoint a (fun j => (l.get j).1) (B, X)
      (fun j => evaluateAmplitudeSlot t (l.get j).2) =
      polynomialWord (dynkinProduct a B) X (generatorSchemeWord w i t) := by
    rw [polynomialWord_eq_listProduct, ← he]
    simp only [List.map_ofFn, amplitudeWordEndpoint, Function.comp_def]
  rw [hw]
  apply (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg).injective
  rw [exp_polynomialWord, exp_polynomialEndpointScheme a B hB hg]

end PolycyclicRecognition

end

end OAI

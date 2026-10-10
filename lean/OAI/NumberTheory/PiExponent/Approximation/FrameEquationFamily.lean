import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Geometry.CurveContact

namespace OAI

namespace PiExponent.FrameEquationFamily

open scoped BigOperators
open PiExponentApprox

abbrev BoundedWords {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ) :=
  {word : List (Fin (m + 1)) // frameWordCost cost word ≤ bound}

noncomputable def equations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) : BoundedWords cost bound → FramePolynomial m :=
  fun word => polynomialFrameWord m word.1 F

theorem equations_mem {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) (word : BoundedWords cost bound) :
    equations cost bound F word ∈ frameDerivativeIdeal cost bound F :=
  frameWord_mem_derivativeIdeal cost bound F word.1 word.2

theorem span_equations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) :
    Ideal.span (Set.range (equations cost bound F)) =
      frameDerivativeIdeal cost bound F := by
  unfold frameDerivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨word.1, word.2, rfl⟩
  · rintro ⟨word, hword, rfl⟩
    exact ⟨⟨word, hword⟩, rfl⟩

theorem monomialWeight_eq_weight {m : ℕ} (W : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) :
    monomialWeight W d = Finsupp.weight W d := by
  simp only [monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul]

theorem hasWeightedDegreeLE_iff_supportBound {m : ℕ} (W : Fin (m + 1) → ℝ)
    (N : ℝ) (F : FramePolynomial m) :
    HasWeightedDegreeLE W N F ↔ WeightedSliceDegree.SupportBound W N F := by
  simp only [HasWeightedDegreeLE, WeightedSliceDegree.SupportBound, monomialWeight_eq_weight]

theorem equation_hasWeightedDegreeLE {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    HasWeightedDegreeLE W N (equations cost bound F word) :=
  hF.polynomialFrameWord hW word.1

theorem equation_supportBound {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound F word) :=
  (hasWeightedDegreeLE_iff_supportBound W N _).mp
    (equation_hasWeightedDegreeLE cost W bound N F hF hW word)

variable {E : Type*} [Field E] [Algebra ℂ E]

noncomputable def sliceEquations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E) :
    BoundedWords cost bound → MvPolynomial (Fin A.card) E :=
  fun word => WeightedSliceDegree.enumeratedSliceMap A b (equations cost bound F word)

theorem span_sliceEquations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E) :
    Ideal.span (Set.range (sliceEquations cost bound F A b)) =
      (frameDerivativeIdeal cost bound F).map
        (WeightedSliceDegree.enumeratedSliceMap A b).toRingHom := by
  rw [← span_equations cost bound F, Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨equations cost bound F word, ⟨word, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨word, rfl⟩, rfl⟩
    exact ⟨word, rfl⟩

theorem sliceEquation_supportBound {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E)
    (word : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound (fun j : Fin A.card => W (A.equivFin.symm j)) N
      (sliceEquations cost bound F A b word) :=
  WeightedSliceDegree.supportBound_enumeratedSliceMap A b W hW N
    (equations cost bound F word) (equation_supportBound cost W bound N F hF hW word)

theorem sliceEquation_weighted_sum_le {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E)
    (word : BoundedWords cost bound) :
    ∀ d ∈ (sliceEquations cost bound F A b word).support,
      (∑ j ∈ d.support, (d j : ℝ) * W (A.equivFin.symm j)) ≤ N := by
  have h := sliceEquation_supportBound cost W bound N F hF hW A b word
  simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
    nsmul_eq_mul] using h

theorem sliceEquation_eval {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E)
    (word : BoundedWords cost bound) :
    MvPolynomial.aeval (fun j : Fin A.card => b (A.equivFin.symm j))
      (sliceEquations cost bound F A b word) =
      MvPolynomial.aeval b (equations cost bound F word) :=
  AlgHom.congr_fun (WeightedSliceDegree.enumeratedSliceMap_eval (C := ℂ) A b)
    (equations cost bound F word)

end PiExponent.FrameEquationFamily

end OAI

import OAI.Analysis.KadisonSimilarity.FreeProduct.FreePairWords
import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeDihedral

namespace OAI

/-! The exact Gram matrices of the regrouped free-product word vectors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

section Products
variable {R : Type*} [Monoid R]

theorem prod_pairWord {n : ℕ} (a d : Fin n → R) :
    (pairWord a d).prod = (List.ofFn (fun i => a i * d i)).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairWord, List.prod_cons, ih, List.ofFn_succ, Fin.tail, mul_assoc]

end Products

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem trace_star (x : P) : G.trace (star x) = star (G.trace x) := by
  calc
    _ = inner ℂ (G.vector x) (G.vector 1) := by rw [G.inner_vector, mul_one]
    _ = star (inner ℂ (G.vector 1) (G.vector x)) := (inner_conj_symm _ _).symm
    _ = _ := by rw [G.inner_vector, star_one, one_mul]

end TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem inner_tracialWordTensor (n : ℕ) (d e : D) (b f : A)
    (a a' : Fin n → A) (c c' : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (tracialWordTensor G A D n d b a c ha hc)
      (tracialWordTensor G A D n e f a' c' ha' hc') =
      G.trace (star (d : P) * e) * G.trace (star (b : P) * f) *
        ((∏ i, G.trace (star (a i : P) * a' i)) *
          ∏ i, G.trace (star (c i : P) * c' i)) := by
  unfold tracialWordTensor
  refine (inner_hilbertTensorInsert (tracialMultiplicityWord G A n b a ha)
    (tracialMultiplicityWord G A n f a' ha') (tracialEndpointWord G D n d c hc)
    (tracialEndpointWord G D n e c' hc')).trans ?_
  unfold tracialMultiplicityWord tracialEndpointWord
  rw [inner_hilbertTensorInsert, inner_completedTensorWord, inner_endpointWord]
  have hA (x y : A) (hx : G.trace (x : P) = 0) (hy : G.trace (y : P) = 0) :
      inner ℂ (G.baseSymmetryLetter A x hx) (G.baseSymmetryLetter A y hy) =
        G.trace (star (x : P) * y) := G.baseVector_inner A x y
  have hD (x y : D) (hx : G.trace (x : P) = 0) (hy : G.trace (y : P) = 0) :
      inner ℂ (G.baseSymmetryLetter D x hx) (G.baseSymmetryLetter D y hy) =
        G.trace (star (x : P) * y) := G.baseVector_inner D x y
  simp only [hA, hD, G.baseVector_inner]
  ring

/-- Scalar freeness gives precisely the inner product of the actual tensors,
including both unrestricted endpoint factors. -/
theorem inner_reducedWord_eq_tensor (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n : ℕ) (d e : D) (b f : A) (a a' : Fin n → A) (c c' : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)))
      (G.vector ((e : P) * alternatingProduct (fun i => (a' i : P))
        (fun i => (c' i : P)) * (f : P))) =
      inner ℂ (tracialWordTensor G A D n d b a c ha hc)
        (tracialWordTensor G A D n e f a' c' ha' hc') := by
  rw [G.inner_vector, inner_tracialWordTensor]
  have hx := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  have hy := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a' i : P)) (fun i => (c' i : P))
    (fun i => (a' i).property) (fun i => (c' i).property) ha' hc'
  have h := hf.symm.trace_full_pairWords G.trace_star hτ G.tracial hx hy
    d.property e.property b.property f.property
  simpa only [prod_pairWord, alternatingProduct, centeredWordPairing_pairWord] using h

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- Different numbers of centered pairs give orthogonal actual word vectors. -/
theorem inner_reducedWord_ne (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n m : ℕ) (hnm : n ≠ m) (d e : D) (b f : A)
    (a : Fin n → A) (c : Fin n → D) (a' : Fin m → A) (c' : Fin m → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)))
      (G.vector ((e : P) * alternatingProduct (fun i => (a' i : P))
        (fun i => (c' i : P)) * (f : P))) = 0 := by
  rw [G.inner_vector]
  have hx := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  have hy := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a' i : P)) (fun i => (c' i : P))
    (fun i => (a' i).property) (fun i => (c' i).property) ha' hc'
  have h := hf.symm.trace_full_pairWords G.trace_star hτ G.tracial hx hy
    d.property e.property b.property f.property
  have hz : centeredWordPairing G.trace (pairWord (fun i => (a i : P))
      (fun i => (c i : P))) (pairWord (fun i => (a' i : P))
      (fun i => (c' i : P))) = 0 :=
    centeredWordPairing_eq_zero_of_length_ne (by simp only [length_pairWord]; omega)
  rw [hz, mul_zero] at h
  simpa only [prod_pairWord, alternatingProduct] using h

end KadisonSimilarity

end

end OAI

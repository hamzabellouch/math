import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordIsometry
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixConjugateAutomorphism

namespace OAI

/-! Matrix conjugation on the dense free-word family. Its scalar Gram
matrix is unchanged, so it extends to the actual tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

def freeWordFamily (p : Σ n, TracialWordParameter G A D n) : H :=
  tracialAlgebraFamily G A D p.1 p.2

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeWordFamily_total (hgen : ReducedWordGenerated G A D) :
    (Submodule.span ℂ (Set.range (G.freeWordFamily A D))).topologicalClosure = ⊤ := by
  have heq : Set.range (G.freeWordFamily A D) = reducedWordVectors G A D := by
    ext x
    constructor
    · rintro ⟨⟨n, p⟩, rfl⟩
      exact ⟨n, p.2.1, p.1.2, (fun i => (p.1.1 i).1), (fun i => (p.2.2 i).1),
        (fun i => (p.1.1 i).2), (fun i => (p.2.2 i).2), rfl⟩
    · rintro ⟨n, d, b, a, c, ha, hc, rfl⟩
      exact ⟨⟨n, (((fun i => ⟨a i, ha i⟩), b), (d, fun i => ⟨c i, hc i⟩))⟩, rfl⟩
  rw [heq]
  exact hgen

def freeConjugatedParameter {n : ℕ} (p : TracialWordParameter G A D n) :
    TracialWordParameter G A D n :=
  (p.1, (matrixConjugateLetter D ι u p.2.1,
    fun i => ⟨matrixConjugateLetter D ι u (p.2.2 i).1,
      (G.trace_matrixConjugateLetter D ι u (p.2.2 i).1).trans (p.2.2 i).2⟩))

def freeConjugatedFamily (p : Σ n, TracialWordParameter G A D n) : H :=
  G.freeWordFamily A D ⟨p.1, G.freeConjugatedParameter A D ι u p.2⟩

private theorem inner_freeWord_same (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n : ℕ) (p q : TracialWordParameter G A D n) :
    inner ℂ (G.freeWordFamily A D ⟨n, p⟩) (G.freeWordFamily A D ⟨n, q⟩) =
      G.trace (star (p.2.1 : P) * q.2.1) * G.trace (star (p.1.2 : P) * q.1.2) *
        ((∏ i, G.trace (star ((p.1.1 i).1 : P) * (q.1.1 i).1)) *
          ∏ i, G.trace (star ((p.2.2 i).1 : P) * (q.2.2 i).1)) := by
  change inner ℂ (tracialAlgebraFamily G A D n p) (tracialAlgebraFamily G A D n q) = _
  rw [tracialFamilyGram G A D hτ hf n p q]
  exact inner_tracialWordTensor G A D n p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (q.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
private theorem inner_freeWord_different (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n m : ℕ) (hnm : n ≠ m)
    (p : TracialWordParameter G A D n) (q : TracialWordParameter G A D m) :
    inner ℂ (G.freeWordFamily A D ⟨n, p⟩) (G.freeWordFamily A D ⟨m, q⟩) = 0 :=
  inner_reducedWord_ne G A D hτ hf n m hnm p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (q.1.1 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

omit [IsClosed (D : Set P)] in
private theorem trace_conjugated_pair (d e : D) :
    G.trace (star (matrixConjugateLetter D ι u d : P) *
      (matrixConjugateLetter D ι u e : P)) = G.trace (star (d : P) * e) := by
  have h : matrixConjugateLetter D ι u (star d * e) =
      star (matrixConjugateLetter D ι u d) * matrixConjugateLetter D ι u e :=
    (map_mul (matrixConjugationAut D ι u) (star d) e).trans
      (congrArg (fun a : D => a * matrixConjugateLetter D ι u e)
        (map_star (matrixConjugationAut D ι u) d))
  rw [← show (matrixConjugateLetter D ι u (star d * e) : P) =
    star (matrixConjugateLetter D ι u d : P) *
      (matrixConjugateLetter D ι u e : P) from congrArg Subtype.val h]
  exact G.trace_matrixConjugateLetter D ι u (star d * e)

theorem freeConjugatedFamily_gram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (p q : Σ n, TracialWordParameter G A D n) :
    inner ℂ (G.freeConjugatedFamily A D ι u p) (G.freeConjugatedFamily A D ι u q) =
      inner ℂ (G.freeWordFamily A D p) (G.freeWordFamily A D q) := by
  obtain ⟨n, p⟩ := p
  obtain ⟨m, q⟩ := q
  unfold freeConjugatedFamily
  by_cases hnm : n = m
  · subst m
    rw [G.inner_freeWord_same A D hτ hf, G.inner_freeWord_same A D hτ hf]
    simp only [freeConjugatedParameter, G.trace_conjugated_pair D ι u]
  · rw [G.inner_freeWord_different A D hτ hf n m hnm,
      G.inner_freeWord_different A D hτ hf n m hnm]

def freeMatrixConjugationIsometry (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) : H →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (G.freeWordFamily A D) (G.freeConjugatedFamily A D ι u)
    (G.freeWordFamily_total A D hgen) (G.freeConjugatedFamily_gram A D ι u hτ hf)

@[simp] theorem freeMatrixConjugationIsometry_family (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D)
    (p : Σ n, TracialWordParameter G A D n) :
    G.freeMatrixConjugationIsometry A D ι u hτ hf hgen (G.freeWordFamily A D p) =
      G.freeConjugatedFamily A D ι u p :=
  denseFamilyIsometry_apply _ _ _ _ p

theorem freeMatrixConjugationIsometry_word (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.freeMatrixConjugationIsometry A D ι u hτ hf hgen
      (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))) =
      G.vector ((matrixConjugateLetter D ι u d : P) *
        alternatingProduct (fun i => (a i : P))
          (fun i => (matrixConjugateLetter D ι u (c i) : P)) * (b : P)) :=
  G.freeMatrixConjugationIsometry_family A D ι u hτ hf hgen
    ⟨n, (((fun i => ⟨a i, ha i⟩), b), (d, fun i => ⟨c i, hc i⟩))⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

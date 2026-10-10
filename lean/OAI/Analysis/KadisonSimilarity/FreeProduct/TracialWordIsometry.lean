import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeWordHilbert
import OAI.Analysis.KadisonSimilarity.Representation.DenseFamilyIsometry
import OAI.Analysis.KadisonSimilarity.Tensor.TensorPacketDensity

namespace OAI

/-! Construction of the completed free-product word inclusions from the
proved Gram identities and totality of elementary tensors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

abbrev CenteredTracialLetter := {a : A // G.trace (a : P) = 0}

def centeredLetterVector (a : CenteredTracialLetter G A) :
    centeredSubspace (G.baseVector A 1) := G.baseSymmetryLetter A a.1 a.2

theorem centeredLetterVector_dense (hτ : G.trace 1 = 1) :
    DenseRange (centeredLetterVector G A) := by
  have hd := denseRange_tracialCenter (G.baseVector A) (G.baseVector_dense A)
  apply hd.mono
  rintro x ⟨a, rfl⟩
  let b : A := a - G.trace (a : P) • 1
  have hb : G.trace (b : P) = 0 := by
    change G.trace ((a : P) - G.trace (a : P) • 1) = 0
    simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  change G.baseVector A b = (tracialCenter (G.baseVector A) a : G.baseSpace A)
  rw [coe_tracialCenter (G.baseGeometry A).trace (G.baseVector A)
    (G.baseVector_inner A) hτ]
  simp only [b, map_sub, map_smul, TracialCornerGeometry.baseGeometry_trace]

abbrev TracialWordParameter (n : ℕ) :=
  ((Fin n → CenteredTracialLetter G A) × A) ×
    (D × (Fin n → CenteredTracialLetter G D))

def tracialTensorFamily (n : ℕ) (p : TracialWordParameter G A D n) :=
  tracialWordTensor G A D n p.2.1 p.1.2 (fun i => (p.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2)

def tracialAlgebraFamily (n : ℕ) (p : TracialWordParameter G A D n) : H :=
  G.vector ((p.2.1 : P) * alternatingProduct (fun i => ((p.1.1 i).1 : P))
    (fun i => ((p.2.2 i).1 : P)) * (p.1.2 : P))

theorem tracialTensorFamily_dense (hτ : G.trace 1 = 1) (n : ℕ) :
    (Submodule.span ℂ (Set.range (tracialTensorFamily G A D n))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  apply continuousLinearMap_ext_denseTensorPackets (centeredLetterVector G A)
    (G.baseVector A) (G.baseVector D) (centeredLetterVector G D)
    (centeredLetterVector_dense G A hτ) (G.baseVector_dense A)
    (G.baseVector_dense D) (centeredLetterVector_dense G D hτ)
  intro a b d c
  exact hf ((a, b), (d, c))

theorem tracialFamilyGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n : ℕ) (p q : TracialWordParameter G A D n) :
    inner ℂ (tracialAlgebraFamily G A D n p) (tracialAlgebraFamily G A D n q) =
      inner ℂ (tracialTensorFamily G A D n p) (tracialTensorFamily G A D n q) :=
  inner_reducedWord_eq_tensor G A D hτ hf n p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (q.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

/-- The genuine isometric inclusion of one completed word level. -/
def tracialWordInclusion (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A) (n : ℕ) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (tracialTensorFamily G A D n) (tracialAlgebraFamily G A D n)
    (tracialTensorFamily_dense G A D hτ n) (tracialFamilyGram G A D hτ hf n)

@[simp] theorem tracialWordInclusion_family (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n : ℕ) (p : TracialWordParameter G A D n) :
    tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p) =
      tracialAlgebraFamily G A D n p := by
  unfold tracialWordInclusion
  exact denseFamilyIsometry_apply (tracialTensorFamily G A D n)
    (tracialAlgebraFamily G A D n) (tracialTensorFamily_dense G A D hτ n)
    (tracialFamilyGram G A D hτ hf n) p

theorem tracialWordInclusion_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n m : ℕ) (hnm : n ≠ m)
    (x : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n)
    (y : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) m) :
    inner ℂ (tracialWordInclusion G A D hτ hf n x)
      (tracialWordInclusion G A D hτ hf m y) = 0 := by
  have hp (p : TracialWordParameter G A D n) :
      (innerSL ℂ (tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p))).comp
        (tracialWordInclusion G A D hτ hf m).toContinuousLinearMap = 0 := by
    apply continuousLinearMap_eq_zero_of_total (tracialTensorFamily G A D m)
      (tracialTensorFamily_dense G A D hτ m)
    intro q
    change inner ℂ (tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p))
      (tracialWordInclusion G A D hτ hf m (tracialTensorFamily G A D m q)) = 0
    rw [tracialWordInclusion_family, tracialWordInclusion_family]
    exact inner_reducedWord_ne G A D hτ hf n m hnm p.2.1 q.2.1 p.1.2 q.1.2
      (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
      (fun i => (q.1.1 i).1) (fun i => (q.2.2 i).1)
      (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
      (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)
  have hy : (innerSL ℂ (tracialWordInclusion G A D hτ hf m y)).comp
      (tracialWordInclusion G A D hτ hf n).toContinuousLinearMap = 0 := by
    apply continuousLinearMap_eq_zero_of_total (tracialTensorFamily G A D n)
      (tracialTensorFamily_dense G A D hτ n)
    intro p
    apply inner_eq_zero_symm.mp
    exact congrArg (fun f => f y) (hp p)
  apply inner_eq_zero_symm.mp
  exact congrArg (fun f => f x) hy

theorem tracialWordInclusion_dense_span (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    (Submodule.span ℂ (⋃ n, Set.range (tracialWordInclusion G A D hτ hf n))).topologicalClosure =
      ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨n, d, b, a, c, ha, hc, rfl⟩
  let p : TracialWordParameter G A D n :=
    (((fun i => ⟨a i, ha i⟩), b), (d, (fun i => ⟨c i, hc i⟩)))
  apply Set.mem_iUnion.mpr
  refine ⟨n, tracialTensorFamily G A D n p, ?_⟩
  exact tracialWordInclusion_family G A D hτ hf n p

/-- The completed orthogonal word decomposition, built from freeness. -/
def tracialOrthogonalWordLevels (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H where
  inclusion := tracialWordInclusion G A D hτ hf
  orthogonal := tracialWordInclusion_orthogonal G A D hτ hf
  dense_span := tracialWordInclusion_dense_span G A D hτ hf hgen

/-- Ricard--Xu's regrouped word coordinates follow from tracial freeness. -/
theorem ricardXuWordDecompositionInput : RicardXuWordDecompositionInput G A D := by
  intro hτ _ hf hgen
  refine ⟨tracialOrthogonalWordLevels G A D hτ hf hgen, ?_⟩
  intro n d b a c ha hc
  exact tracialWordInclusion_family G A D hτ hf n
    (((fun i => ⟨a i, ha i⟩), b), (d, (fun i => ⟨c i, hc i⟩)))

end KadisonSimilarity

end

end OAI

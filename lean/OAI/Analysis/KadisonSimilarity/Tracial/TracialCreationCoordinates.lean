import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseSymmetry
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordPrefixRealization

namespace OAI

/-! Elementary reduced-word creation in the actual tracial base spaces.
The normalized symmetry and corner Haar vectors are constructed, so the
only word-model inputs are isometric tensor inclusions and their elementary
multiplication and range formulas. -/

noncomputable section
namespace KadisonSimilarity

/-- Elementary multiplication on two opposite reduced-word subspaces.
This record carries no normalization or complete-prefix assumption. -/
structure ElementaryCreationFormulas {EA ED H : Type*}
    [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
    [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (s : EA) (x : ℕ → ED)
    (DLead ALead : Submodule ℂ H) where
  createA : HilbertTensor EA DLead →ₗᵢ[ℂ] H
  createD : HilbertTensor ED ALead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ ALead
  createD_mem : ∀ w, createD w ∈ DLead
  actionA : ∀ y : DLead, S y = createA (hilbertTensorInsert s y)
  actionD : ∀ n (y : ALead), X n y = createD (hilbertTensorInsert (x n) y)

variable {P H F : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)] {q : D} {hq : IsStarProjection q}
  (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 < a)
  (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- The actual normalized corner Haar vector in the centered base space. -/
def baseHaarLetter (n : ℕ) : centeredSubspace (G.baseVector D 1) :=
  ⟨G.baseVector D (haarCornerLetter z a n),
    tracial_vector_mem_centered (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).inner_vector _
      (haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htrace hhaar n)⟩

@[simp] theorem baseHaarLetter_coe (n : ℕ) :
    (G.baseHaarLetter D z ha htrace hhaar n : G.baseSpace D) =
      G.baseVector D (haarCornerLetter z a n) := rfl

/-- The normalized trace and the exact initial-projection identity give
Hilbert norm one for each positive Haar power. -/
theorem norm_baseHaarLetter (n : ℕ) :
    ‖G.baseHaarLetter D z ha htrace hhaar n‖ = 1 := by
  have hinner : inner ℂ (G.baseVector D (haarCornerLetter z a n))
      (G.baseVector D (haarCornerLetter z a n)) = 1 := by
    rw [G.baseVector_inner]
    change (G.baseGeometry D).trace
      (star (haarCornerLetter z a n) * haarCornerLetter z a n) = 1
    rw [star_haarCornerLetter_mul_self z ha.le, map_smul, smul_eq_mul]
    change ((a⁻¹ : ℝ) : ℂ) * G.trace (q : P) = 1
    rw [htrace, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne')]
  have hsq : ‖G.baseVector D (haarCornerLetter z a n)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    rfl
  change ‖G.baseVector D (haarCornerLetter z a n)‖ = 1
  nlinarith [norm_nonneg (G.baseVector D (haarCornerLetter z a n))]

end TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (W : TracialHeadCoordinates (G.baseGeometry D) G D.subtype F)
  [W.vacuum.HasOrthogonalProjection]
  (s : A) (hzero : G.trace (s : P) = 0)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- The standard free-product model supplies these elementary word
identities. All letters and tensor factors are the actual centered tracial
base spaces; no complete-prefix estimate is part of the data. -/
abbrev TracialCreationFormulas (ALead : Submodule ℂ H) :=
  ElementaryCreationFormulas (G.left (s : P))
    (fun n => G.left ((haarCornerLetter z a n : D) : P))
    (G.baseSymmetryLetter A s hzero) (G.baseHaarLetter D z ha htrace hhaar)
    W.vacuumᗮ ALead

namespace TracialCreationFormulas

variable {G A D W s hzero z ha htrace hhaar} {ALead : Submodule ℂ H}
  (C : TracialCreationFormulas G A D W s hzero z ha htrace hhaar ALead)

/-- Normalize the elementary creation data using the proved norms of the
actual symmetry and corner Haar vectors. -/
def toAlternatingCreationCoordinates (hself : star s = s) (hsquare : s * s = 1)
    (hτ : G.trace 1 = 1) :
    AlternatingCreationCoordinates (centeredSubspace (G.baseVector A 1))
      (centeredSubspace (G.baseVector D 1)) (G.left (s : P))
      (fun n => G.left ((haarCornerLetter z a n : D) : P)) W.vacuumᗮ where
  ALead := ALead
  s := G.baseSymmetryLetter A s hzero
  x := G.baseHaarLetter D z ha htrace hhaar
  norm_s := G.norm_baseSymmetryLetter A s hzero hself hsquare hτ
  norm_x := G.norm_baseHaarLetter D z ha htrace hhaar
  createA := C.createA
  createD := C.createD
  createA_mem := C.createA_mem
  createD_mem := C.createD_mem
  actionA := C.actionA
  actionD := C.actionD

include C in
omit [CompleteSpace F] [W.vacuum.HasOrthogonalProjection] in
/-- The actual alternating left multiplier is isometric on the nonvacuum
head space. This is derived from the two elementary word formulas. -/
theorem prefix_isometry (hself : star s = s) (hsquare : s * s = 1)
    (hτ : G.trace 1 = 1) (m n : ℕ) (y : H) (hy : y ∈ W.vacuumᗮ) :
    ‖G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n) y‖ = ‖y‖ :=
  tracialWordPrefix_isometry W z a (s : P)
    (C.toAlternatingCreationCoordinates hself hsquare hτ) m n y hy

omit [W.vacuum.HasOrthogonalProjection] [IsClosed (A : Set P)] in
/-- The actual prefix bound follows from algebra norms and holds uniformly
in the Haar frequency. -/
theorem prefix_bound (hself : star s = s) (hsquare : s * s = 1) (m n : ℕ) :
    ‖G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)‖ ≤
      ((Real.sqrt a)⁻¹) ^ m := by
  have hselfP : star (s : P) = (s : P) := congrArg (fun x : A => (x : P)) hself
  have hsquareP : (s : P) * (s : P) = 1 := congrArg (fun x : A => (x : P)) hsquare
  exact norm_tracialWordPrefix_le z a (s : P) hselfP hsquareP m n

/-- The concrete repeated-multiplicity insertion, together with raw word
factorization and level actions, gives the propagation realization. Complete
prefix isometry and uniform boundedness are both proved by this constructor. -/
def repeatedWordRealization (hself : star s = s) (hsquare : s * s = 1)
    (hτ : G.trace 1 = 1) (m : ℕ) (Y : H →L[ℂ] H)
    (B₀ : G.baseSpace A →L[ℂ] G.baseSpace A)
    (Bₖ : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (word : ℕ → WordMultiplicity (G.baseVector A 1) (m + 1) →ₗᵢ[ℂ] H)
    (small : G.baseSpace A →L[ℂ] H)
    (hsmall : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖)
    (hlevelzero : ∀ v, Y (small v) = small (B₀ v))
    (hlevel : ∀ n v, Y (word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)) =
      word n (Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)))
    (hsupport : ∀ v, G.left (q : P) (small v) = small v)
    (hword : ∀ n (v : A), word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseVector A v)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P) (small (G.baseVector A v)))) :
    TracialRepeatedWordRealization W z a Y B₀ Bₖ := by
  have hword' (n : ℕ) (v : G.baseSpace A) : word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P) (small v)) := by
    exact (G.baseVector_dense A).induction_on v
      (isClosed_eq (by fun_prop) (by fun_prop)) (hword n)
  have hselfP : star (s : P) = (s : P) := congrArg (fun x : A => (x : P)) hself
  have hsquareP : (s : P) * (s : P) = 1 := congrArg (fun x : A => (x : P)) hsquare
  exact tracialRepeatedWordRealizationOfCreation W z a (s : P) hselfP hsquareP
    (C.toAlternatingCreationCoordinates hself hsquare hτ) m Y B₀ Bₖ
    (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1))
    word small hsmall hlevelzero hlevel hsupport hword'

end TracialCreationFormulas
end KadisonSimilarity

end

end OAI

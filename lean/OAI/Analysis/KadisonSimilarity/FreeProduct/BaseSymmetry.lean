import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseGeometry
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordMultiplicities

namespace OAI

/-! A trace-zero symmetry of the actual base algebra supplies the normalized
centered letter and its represented selfadjoint involution. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

/-- A trace-zero base element is an actual centered base Hilbert vector. -/
def baseSymmetryLetter (s : A) (hzero : G.trace (s : P) = 0) :
    centeredSubspace (G.baseVector A 1) :=
  ⟨G.baseVector A s,
    tracial_vector_mem_centered (G.baseGeometry A).trace (G.baseGeometry A).vector
      (G.baseGeometry A).inner_vector s hzero⟩

@[simp] theorem baseSymmetryLetter_coe (s : A) (hzero : G.trace (s : P) = 0) :
    (G.baseSymmetryLetter A s hzero : G.baseSpace A) = G.baseVector A s := rfl

/-- Trace normalization and the symmetry relation give norm one, rather than
requiring a separately chosen unit vector in the centered space. -/
theorem norm_baseSymmetryLetter (s : A) (hzero : G.trace (s : P) = 0)
    (hself : star s = s) (hsquare : s * s = 1) (htrace : G.trace 1 = 1) :
    ‖G.baseSymmetryLetter A s hzero‖ = 1 := by
  have hsq : ‖G.baseVector A s‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    change Complex.re ((G.baseGeometry A).trace (star s * s)) = 1
    rw [hself, hsquare]
    exact congrArg Complex.re (G.baseGeometry_trace_one A htrace)
  change ‖G.baseVector A s‖ = 1
  nlinarith [norm_nonneg (G.baseVector A s)]

omit [IsClosed (A : Set P)] in
/-- Selfadjointness passes through the actual base representation. -/
theorem baseSymmetry_selfadjoint (s : A) (hself : star s = s) :
    IsSelfAdjoint (G.baseRepresentation A s) := by
  change star (G.baseRepresentation A s) = G.baseRepresentation A s
  rw [← map_star, hself]

omit [IsClosed (A : Set P)] in
/-- The represented base symmetry squares to the identity operator. -/
theorem baseSymmetry_square (s : A) (hsquare : s * s = 1) :
    (G.baseRepresentation A s).comp (G.baseRepresentation A s) =
      ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  change G.baseRepresentation A s * G.baseRepresentation A s = 1
  rw [← map_mul, hsquare, map_one]

omit [IsClosed (A : Set P)] in
/-- The represented symmetry is an actual unitary bounded operator. -/
def baseSymmetryUnitary (s : A) (hself : star s = s) (hsquare : s * s = 1) :
    unitary (G.baseSpace A →L[ℂ] G.baseSpace A) :=
  ⟨G.baseRepresentation A s, by
    have hstar := (G.baseSymmetry_selfadjoint A s hself).star_eq
    have hsq : G.baseRepresentation A s * G.baseRepresentation A s = 1 :=
      G.baseSymmetry_square A s hsquare
    exact ⟨by rw [hstar, hsq], by rw [hstar, hsq]⟩⟩

omit [IsClosed (A : Set P)] in
/-- The unitary relation gives contractivity even if the Hilbert space were
trivial; trace normalization is only needed for the centered letter's norm. -/
theorem norm_baseSymmetry_le_one (s : A) (hself : star s = s) (hsquare : s * s = 1) :
    ‖G.baseRepresentation A s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := ContinuousLinearMap.norm_map_of_mem_unitary
    (G.baseSymmetryUnitary A s hself hsquare).property x
  simpa only [baseSymmetryUnitary, one_mul] using h.le

omit [IsClosed (A : Set P)] in
/-- The compressed ambient symmetry and the restricted base representation
are exactly the same operator. -/
theorem baseSymmetry_compression (s : A) :
    G.baseCompression A (s : P) = G.baseRepresentation A s :=
  G.baseCompression_subalgebra A s

/-- The actual base symmetry determines all normalized repeated-letter
inclusions required by the word multiplicities. -/
def baseSymmetryRepeatedInclusion (s : A) (hzero : G.trace (s : P) = 0)
    (hself : star s = s) (hsquare : s * s = 1) (htrace : G.trace 1 = 1) (k : ℕ) :
    G.baseSpace A →ₗᵢ[ℂ] WordMultiplicity (G.baseVector A 1) k :=
  repeatedMultiplicityInclusion (G.baseVector A 1) (G.baseSymmetryLetter A s hzero)
    (G.norm_baseSymmetryLetter A s hzero hself hsquare htrace) k

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

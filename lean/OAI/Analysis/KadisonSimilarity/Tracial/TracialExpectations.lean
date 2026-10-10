import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! The trace-pairing description of conditional expectation. Its uniqueness,
bimodule law, tower law, and Hilbert projection formula are derived here. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The minimal trace-pairing data for expectation onto a tracial subalgebra.
Existence is required only when a subalgebra is realized as a von Neumann
subalgebra; no existence assertion for arbitrary star subalgebras is made. -/
structure TracialExpectation (τ : P →ₗ[ℂ] ℂ) (A : StarSubalgebra ℂ P) where
  map : P →ₗ[ℂ] P
  range : ∀ x, map x ∈ A
  pairing : ∀ x c, c ∈ A → τ (c * map x) = τ (c * x)

namespace TracialCornerGeometry

/-- Faithfulness of the algebra-vector realization implies faithfulness of
its positive trace pairing. -/
theorem trace_faithful (G : TracialCornerGeometry P H)
    (hfaithful : Function.Injective G.vector) (x : P)
    (hx : G.trace (star x * x) = 0) : x = 0 := by
  apply hfaithful
  rw [map_zero]
  exact inner_self_eq_zero.mp (by rw [G.inner_vector, hx])

end TracialCornerGeometry

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {A : StarSubalgebra ℂ P}
  (E : TracialExpectation τ A)

/-- Expectation preserves the trace by testing its pairing with the unit. -/
theorem trace_map (x : P) : τ (E.map x) = τ x := by
  simpa only [one_mul] using E.pairing x 1 A.one_mem

variable (hf : ∀ x, τ (star x * x) = 0 → x = 0)

include hf

/-- The trace pairing determines each expectation value uniquely. -/
theorem eq_of_pairings (x y : P) (hy : y ∈ A)
    (hxy : ∀ c, c ∈ A → τ (c * x) = τ (c * y)) : E.map x = y :=
  expectation_eq_of_trace_pairings τ A hf E.map E.range E.pairing x y hy hxy

theorem map_of_mem {x : P} (hx : x ∈ A) : E.map x = x :=
  E.eq_of_pairings hf x x hx (fun _ _ => rfl)

@[simp] theorem map_one : E.map 1 = 1 := E.map_of_mem hf A.one_mem

@[simp] theorem map_map (x : P) : E.map (E.map x) = E.map x :=
  E.map_of_mem hf (E.range x)

/-- Left bimodularity follows from the trace-pairing characterization alone. -/
theorem map_mul_left (a x : P) (ha : a ∈ A) : E.map (a * x) = a * E.map x := by
  apply E.eq_of_pairings hf _ _ (A.mul_mem ha (E.range x))
  intro c hc
  simpa only [mul_assoc] using (E.pairing x (c * a) (A.mul_mem hc ha)).symm

/-- Right bimodularity additionally uses traciality. -/
theorem map_mul_right (htr : ∀ x y, τ (x * y) = τ (y * x))
    (x b : P) (hb : b ∈ A) : E.map (x * b) = E.map x * b := by
  apply E.eq_of_pairings hf _ _ (A.mul_mem (E.range x) hb)
  intro c hc
  calc
    τ (c * (x * b)) = τ ((b * c) * x) := by rw [← mul_assoc, htr, mul_assoc]
    _ = τ ((b * c) * E.map x) := (E.pairing x (b * c) (A.mul_mem hb hc)).symm
    _ = τ (c * (E.map x * b)) := by rw [mul_assoc, htr, mul_assoc]

theorem bimodule (htr : ∀ x y, τ (x * y) = τ (y * x))
    (a b x : P) (ha : a ∈ A) (hb : b ∈ A) :
    E.map (a * x * b) = a * E.map x * b := by
  rw [E.map_mul_right hf htr _ b hb, E.map_mul_left hf a x ha]

/-- Nested tracial expectations compose to the smaller one. -/
theorem tower {C : StarSubalgebra ℂ P} (EC : TracialExpectation τ C)
    (hAC : A ≤ C) (x : P) : E.map (EC.map x) = E.map x := by
  apply E.eq_of_pairings hf _ _ (E.range x)
  intro c hc
  rw [EC.pairing x c (hAC hc), E.pairing x c hc]

/-- Faithful trace pairings separate two elements of any star subalgebra. -/
theorem eq_of_trace_tests (B : StarSubalgebra ℂ P) (x y : P)
    (hx : x ∈ B) (hy : y ∈ B)
    (htest : ∀ c, c ∈ B → τ (c * x) = τ (c * y)) : x = y := by
  apply sub_eq_zero.mp
  apply hf
  have hc : star (x - y) ∈ B := star_mem (B.sub_mem hx hy)
  rw [mul_sub, map_sub, htest _ hc, sub_self]

/-- The expectation tower identity is only needed on a specified word
subalgebra. This version applies when the base expectation of those words
lands in a smaller algebra contained in the intermediate algebra; the whole
base algebra need not be contained in that intermediate algebra. -/
theorem restricted_tower {C S B : StarSubalgebra ℂ P}
    (EC : TracialExpectation τ C) (hCS : C ≤ S) (hBA : B ≤ A) (hBC : B ≤ C)
    (hmap : ∀ x, x ∈ S → E.map x ∈ B) (x : P) (hx : x ∈ S) :
    E.map (EC.map x) = E.map x := by
  apply eq_of_trace_tests hf B _ _
    (hmap _ (hCS (EC.range x))) (hmap _ hx)
  intro c hc
  rw [E.pairing _ c (hBA hc), EC.pairing x c (hBC hc), E.pairing x c (hBA hc)]

/-- Scalar freeness now gives the free-compression expectation formula for
this actual expectation map. -/
theorem free_compression (hτ : τ 1 = 1)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    {D : StarSubalgebra ℂ P} (hfree : ScalarFree τ D A)
    {e b : P} (he : e ∈ D) (hb : b ∈ A) (hb0 : τ b = 0) :
    E.map (e * b * e) = (τ e) ^ 2 • b :=
  expectation_free_compression τ hτ htr hf hfree E.map E.range E.pairing he hb hb0

end TracialExpectation

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (E : TracialExpectation G.trace A)

/-- Conditional expectation on algebra vectors is exactly orthogonal
projection onto the actual closed base Hilbert space. -/
theorem expectation_base_projection (x : P) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector x) =
      G.baseVector A ⟨E.map x, E.range x⟩ := by
  apply ext_inner_left ℂ
  intro y
  refine (G.baseVector_dense A).induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.vector x) =
    inner ℂ (G.vector (a : P)) (G.vector (E.map x))
  rw [G.inner_vector, G.inner_vector]
  exact (E.pairing x (star (a : P)) (star_mem a.property)).symm

/-- Expectation is contractive for the tracial Hilbert norm. -/
theorem expectation_vector_norm_le (x : P) : ‖G.vector (E.map x)‖ ≤ ‖G.vector x‖ := by
  change ‖G.baseVector A ⟨E.map x, E.range x⟩‖ ≤ _
  rw [← G.expectation_base_projection A E]
  calc
    _ ≤ ‖(G.baseInclusion A).toContinuousLinearMap.adjoint‖ * ‖G.vector x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖G.vector x‖ := by
      gcongr
      simpa only [ContinuousLinearMap.adjoint.norm_map] using
        (G.baseInclusion A).norm_toContinuousLinearMap_le
    _ = ‖G.vector x‖ := one_mul _

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseGeometry
import Mathlib.Topology.Algebra.StarSubalgebra
import OAI.Analysis.KadisonSimilarity.Tracial.GeneratedGNSModels

namespace OAI

/-! The bounded elements in the L² closure of a star subalgebra form an
actual norm-closed star subalgebra. Multiplication is obtained from the
commuting left and right tracial actions, rather than assumed as a property
of a proposed generated algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

open scoped CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The algebra-vector map is norm continuous because it is the left
representation evaluated at the identity vector. -/
theorem vector_continuous : Continuous G.vector := by
  have he : G.vector = fun a => G.left a (G.vector 1) := by
    funext a
    rw [G.left_vector, mul_one]
  rw [he]
  exact (map_continuous G.left).clm_apply continuous_const

/-- Inclusion of algebras induces inclusion of their closed Hilbert spans. -/
theorem baseSpace_mono {S T : StarSubalgebra ℂ P} (hST : S ≤ T) :
    G.baseSpace S ≤ G.baseSpace T := by
  change closure (Set.range (G.baseAlgebraVectors S)) ⊆
    closure (Set.range (G.baseAlgebraVectors T))
  apply closure_mono
  rintro x ⟨a, rfl⟩
  exact ⟨⟨(a : P), hST a.property⟩, rfl⟩

/-- Taking the norm closure of the algebra does not change its L² span. -/
theorem baseSpace_topologicalClosure (S : StarSubalgebra ℂ P) :
    G.baseSpace S.topologicalClosure = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors S.topologicalClosure)) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    have hc : closure (S : Set P) ⊆ G.vector ⁻¹' (G.baseSpace S : Set H) := by
      apply closure_minimal _ ((G.baseSpace S).isClosed.preimage G.vector_continuous)
      intro b hb
      exact (G.baseVector S ⟨b, hb⟩).property
    exact hc a.property
  · exact G.baseSpace_mono S.le_topologicalClosure

section ClosedSeed

variable (S : StarSubalgebra ℂ P) [hSclosed : IsClosed (S : Set P)]

/-- An element whose vector lies in the closed subspace preserves that
subspace under left multiplication, by right multiplication on dense
algebra vectors. -/
theorem left_preserves_baseSpace_of_vector_mem {x : P}
    (hx : G.vector x ∈ G.baseSpace S) (y : H) (hy : y ∈ G.baseSpace S) :
    G.left x y ∈ G.baseSpace S := by
  have h (z : G.baseSpace S) : G.left x (z : H) ∈ G.baseSpace S := by
    refine (G.baseVector_dense S).induction_on z
      ((G.baseSpace S).isClosed.preimage
        ((G.left x).continuous.comp continuous_subtype_val)) ?_
    intro a
    change G.left x (G.vector (a : P)) ∈ G.baseSpace S
    rw [G.left_vector, ← G.right_vector]
    exact G.baseSpace_right_invariant S a (G.vector x) hx
  exact h ⟨y, hy⟩

/-- The same closed subspace is preserved by tracial conjugation. -/
theorem conjugation_preserves_baseSpace (y : H) (hy : y ∈ G.baseSpace S) :
    G.conjugation y ∈ G.baseSpace S := by
  rw [← G.baseGeometry_conjugation_coe S (⟨y, hy⟩ : G.baseSpace S)]
  exact ((G.baseGeometry S).conjugation (⟨y, hy⟩ : G.baseSpace S)).property

/-- The actual bounded algebra lying in the L² closure of `S`. -/
def l2ClosureAlgebra : StarSubalgebra ℂ P where
  carrier := {x | G.vector x ∈ G.baseSpace S}
  zero_mem' := by
    change G.vector 0 ∈ (G.baseSpace S).toSubmodule
    rw [map_zero]
    exact (G.baseSpace S).toSubmodule.zero_mem
  add_mem' {x y} hx hy := by
    change G.vector (x + y) ∈ (G.baseSpace S).toSubmodule
    rw [map_add]
    exact (G.baseSpace S).toSubmodule.add_mem hx hy
  one_mem' := (G.baseVector S 1).property
  mul_mem' {x y} hx hy := by
    change G.vector (x * y) ∈ G.baseSpace S
    rw [← G.left_vector]
    exact G.left_preserves_baseSpace_of_vector_mem S hx (G.vector y) hy
  algebraMap_mem' c := by
    change G.vector (algebraMap ℂ P c) ∈ G.baseSpace S
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    exact (G.baseSpace S).smul_mem c (G.baseVector S 1).property
  star_mem' {x} hx := by
    change G.vector (star x) ∈ G.baseSpace S
    rw [← G.conjugation_vector]
    exact G.conjugation_preserves_baseSpace S (G.vector x) hx

include hSclosed in
@[simp] theorem mem_l2ClosureAlgebra (x : P) :
    x ∈ G.l2ClosureAlgebra S ↔ G.vector x ∈ G.baseSpace S := Iff.rfl

instance l2ClosureAlgebra_isClosed : IsClosed (G.l2ClosureAlgebra S : Set P) :=
  (G.baseSpace S).isClosed.preimage G.vector_continuous

include hSclosed in
/-- Every original algebra element lies in the constructed bounded closure. -/
theorem le_l2ClosureAlgebra : S ≤ G.l2ClosureAlgebra S := by
  intro x hx
  exact (G.baseVector S ⟨x, hx⟩).property

include hSclosed in
/-- Membership gives exactly the required L² approximation by the original
algebra vectors, with no additional generated-algebra hypothesis. -/
theorem l2ClosureAlgebra_vector_mem (x : G.l2ClosureAlgebra S) :
    G.vector (x : P) ∈ closure (Set.range (G.baseAlgebraVectors S)) := x.property

/-- Passing to the constructed bounded algebra leaves the Hilbert space
unchanged. -/
theorem baseSpace_l2ClosureAlgebra : G.baseSpace (G.l2ClosureAlgebra S) = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors (G.l2ClosureAlgebra S))) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    exact a.property
  · exact G.baseSpace_mono (G.le_l2ClosureAlgebra S)

end ClosedSeed

/-- The bounded L²-generated algebra of an arbitrary star subalgebra,
constructed by first taking its norm closure. -/
def l2GeneratedAlgebra (S : StarSubalgebra ℂ P) : StarSubalgebra ℂ P := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact G.l2ClosureAlgebra S.topologicalClosure

instance l2GeneratedAlgebra_isClosed (S : StarSubalgebra ℂ P) :
    IsClosed (G.l2GeneratedAlgebra S : Set P) := by
  unfold l2GeneratedAlgebra
  infer_instance

/-- The original seed algebra is contained in its constructed L²-generated
algebra. -/
theorem le_l2GeneratedAlgebra (S : StarSubalgebra ℂ P) : S ≤ G.l2GeneratedAlgebra S := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact S.le_topologicalClosure.trans (G.le_l2ClosureAlgebra S.topologicalClosure)

/-- The generated algebra has precisely the original seed's Hilbert span. -/
theorem baseSpace_l2GeneratedAlgebra (S : StarSubalgebra ℂ P) :
    G.baseSpace (G.l2GeneratedAlgebra S) = G.baseSpace S := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact (G.baseSpace_l2ClosureAlgebra S.topologicalClosure).trans
    (G.baseSpace_topologicalClosure S)

/-- Algebra-vector density of the seed is built into the construction,
including when the seed is merely the algebraic factor algebra. -/
theorem l2GeneratedAlgebra_vector_mem (S : StarSubalgebra ℂ P)
    (x : G.l2GeneratedAlgebra S) :
    G.vector (x : P) ∈ closure (Set.range (G.baseAlgebraVectors S)) := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  have hx : G.vector (x : P) ∈ G.baseSpace S.topologicalClosure := x.property
  rw [G.baseSpace_topologicalClosure S] at hx
  exact hx

/-- The concrete bounded algebra generated in L² by two prescribed factors. -/
def l2FactorAlgebra (A D : StarSubalgebra ℂ P) : StarSubalgebra ℂ P :=
  G.l2GeneratedAlgebra (factorAlgebra A D)

instance l2FactorAlgebra_isClosed (A D : StarSubalgebra ℂ P) :
    IsClosed (G.l2FactorAlgebra A D : Set P) :=
  G.l2GeneratedAlgebra_isClosed (factorAlgebra A D)

theorem left_le_l2FactorAlgebra (A D : StarSubalgebra ℂ P) : A ≤ G.l2FactorAlgebra A D := by
  intro a ha
  apply G.le_l2GeneratedAlgebra (factorAlgebra A D)
  exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ha)

theorem right_le_l2FactorAlgebra (A D : StarSubalgebra ℂ P) : D ≤ G.l2FactorAlgebra A D := by
  intro a ha
  apply G.le_l2GeneratedAlgebra (factorAlgebra A D)
  exact StarAlgebra.subset_adjoin ℂ _ (Or.inr ha)

/-- Algebra vectors of the two generating factors are dense in the
constructed algebra's tracial Hilbert space. -/
theorem l2FactorAlgebra_vector_mem (A D : StarSubalgebra ℂ P)
    (x : G.l2FactorAlgebra A D) :
    G.vector (x : P) ∈ closure (Set.range
      (G.vector.comp (factorAlgebra A D).subtype.toLinearMap)) :=
  G.l2GeneratedAlgebra_vector_mem (factorAlgebra A D) x

/-- In its concrete Hilbert subspace, the constructed algebra is generated
by the two original factors. -/
theorem l2FactorAlgebra_generation (A D : StarSubalgebra ℂ P) :
    (G.baseGeometry (G.l2FactorAlgebra A D)).FactorsTraciallyGenerate
      (A.comap (G.l2FactorAlgebra A D).subtype)
      (D.comap (G.l2FactorAlgebra A D).subtype) :=
  G.factorsTraciallyGenerate_of_L2_generation A D (G.l2FactorAlgebra A D)
    (G.left_le_l2FactorAlgebra A D) (G.right_le_l2FactorAlgebra A D)
    (G.l2FactorAlgebra_vector_mem A D)

variable [PartialOrder P] [StarOrderedRing P]

/-- The same generation statement holds in the canonical GNS model of
the constructed algebra, without a separate density hypothesis. -/
theorem l2FactorAlgebra_native_generation (τ : P →ₚ[ℂ] ℂ)
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) (A D : StarSubalgebra ℂ P) :
    let L := (gnsTracialGeometry τ htr).l2FactorAlgebra A D
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).FactorsTraciallyGenerate
      (A.comap L.subtype) (D.comap L.subtype) := by
  let G := gnsTracialGeometry τ htr
  let L := G.l2FactorAlgebra A D
  exact restrictedGNS_factorsTraciallyGenerate τ htr A D L
    (G.left_le_l2FactorAlgebra A D) (G.right_le_l2FactorAlgebra A D)
    (G.l2FactorAlgebra_vector_mem A D)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

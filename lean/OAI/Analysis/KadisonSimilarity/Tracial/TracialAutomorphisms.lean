import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace

namespace OAI

/-! Hilbert-space implementation of trace-preserving automorphisms. The
implementation and its covariance are constructed from dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (θ : P ≃⋆ₐ[ℂ] P)
  (hθ : ∀ a, G.trace (θ a) = G.trace a)

include hθ in
theorem automorphism_vector_norm (a : P) : ‖G.vector (θ a)‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.inner_vector, G.inner_vector, ← map_star θ, ← map_mul θ, hθ]

/-- Extension of the automorphism on bounded algebra vectors. -/
def automorphismIsometry : H →ₗᵢ[ℂ] H :=
  (G.vector.comp θ.toAlgEquiv.toLinearMap).extendOfIsometry G.dense_vector
    (G.automorphism_vector_norm θ hθ)

@[simp] theorem automorphismIsometry_vector (a : P) :
    G.automorphismIsometry θ hθ (G.vector a) = G.vector (θ a) :=
  LinearMap.extendOfIsometry_eq _ G.dense_vector (G.automorphism_vector_norm θ hθ) a

include hθ in
theorem trace_symm_automorphism (a : P) : G.trace (θ.symm a) = G.trace a := by
  simpa only [θ.apply_symm_apply] using (hθ (θ.symm a)).symm

theorem automorphismIsometry_surjective : Function.Surjective (G.automorphismIsometry θ hθ) := by
  intro x
  refine ⟨G.automorphismIsometry θ.symm (G.trace_symm_automorphism θ hθ) x, ?_⟩
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro a
  simp only [automorphismIsometry_vector, θ.apply_symm_apply]

/-- The actual unitary implementation of a trace-preserving automorphism. -/
def automorphismUnitary : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (G.automorphismIsometry θ hθ)
    (G.automorphismIsometry_surjective θ hθ)

@[simp] theorem automorphismUnitary_vector (a : P) :
    G.automorphismUnitary θ hθ (G.vector a) = G.vector (θ a) :=
  G.automorphismIsometry_vector θ hθ a

/-- Multiplication covariance extends from the algebra to the whole Hilbert space. -/
theorem automorphismUnitary_left (a : P) (x : H) :
    G.automorphismUnitary θ hθ (G.left a x) =
      G.left (θ a) (G.automorphismUnitary θ hθ x) := by
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [G.left_vector, automorphismUnitary_vector, map_mul]

theorem automorphismUnitary_fixes_base (A : StarSubalgebra ℂ P)
    (hA : ∀ a : A, θ (a : P) = (a : P)) (x : G.baseSpace A) :
    G.automorphismUnitary θ hθ (x : H) = (x : H) := by
  refine (G.baseVector_dense A).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change G.automorphismUnitary θ hθ (G.vector (a : P)) = G.vector (a : P)
  rw [G.automorphismUnitary_vector, hA]

/-- A trace-preserving algebraic group action gives a unitary representation. -/
def automorphismRepresentation {Γ : Type*} [Group Γ]
    (α : Γ →* (P ≃⋆ₐ[ℂ] P)) (hα : ∀ g a, G.trace (α g a) = G.trace a) :
    Γ →* unitary (H →L[ℂ] H) where
  toFun g := Unitary.linearIsometryEquiv.symm (G.automorphismUnitary (α g) (hα g))
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    change G.automorphismUnitary (α 1) (hα 1) (G.vector a) = G.vector a
    rw [G.automorphismUnitary_vector, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    change G.automorphismUnitary (α (g * h)) (hα (g * h)) (G.vector a) =
      G.automorphismUnitary (α g) (hα g)
        (G.automorphismUnitary (α h) (hα h) (G.vector a))
    simp only [G.automorphismUnitary_vector, map_mul]
    rfl

@[simp] theorem automorphismRepresentation_vector {Γ : Type*} [Group Γ]
    (α : Γ →* (P ≃⋆ₐ[ℂ] P)) (hα : ∀ g a, G.trace (α g a) = G.trace a)
    (g : Γ) (a : P) :
    (G.automorphismRepresentation α hα g : H →L[ℂ] H) (G.vector a) =
      G.vector (α g a) := G.automorphismUnitary_vector (α g) (hα g) a

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeProductMatrixExtension
import OAI.Analysis.KadisonSimilarity.Tracial.TracialAutomorphisms

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The bounded factor algebra, before taking its tracial L² closure. -/
def factorAlgebra (A D : StarSubalgebra ℂ P) : StarSubalgebra ℂ P :=
  StarAlgebra.adjoin ℂ ((A : Set P) ∪ (D : Set P))

/-- Ordinary tracial generation by the two factors. This is geometric density
of algebra vectors, independent of any operator intertwining statement. -/
def FactorsTraciallyGenerate (A D : StarSubalgebra ℂ P) : Prop :=
  DenseRange (G.vector.comp (factorAlgebra A D).subtype.toLinearMap)

include G in
/-- A trace-preserving homomorphism is isometric on the tracial algebra vectors. -/
theorem hom_vector_norm (Φ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a) (a : P) :
    ‖G.vector (Φ a)‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.inner_vector, G.inner_vector, ← map_star Φ, ← map_mul Φ, hΦ]

/-- The actual L² isometry of a trace-preserving ambient homomorphism. -/
def homIsometry (Φ : P →⋆ₐ[ℂ] P) (hΦ : ∀ a, G.trace (Φ a) = G.trace a) :
    H →ₗᵢ[ℂ] H :=
  (G.vector.comp Φ.toAlgHom.toLinearMap).extendOfIsometry G.dense_vector
    (G.hom_vector_norm Φ hΦ)

@[simp] theorem homIsometry_vector (Φ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a) (a : P) :
    G.homIsometry Φ hΦ (G.vector a) = G.vector (Φ a) :=
  LinearMap.extendOfIsometry_eq _ G.dense_vector (G.hom_vector_norm Φ hΦ) a

/-- Trace preservation turns tracial generation into uniqueness of ambient
extensions of the two factor maps. -/
theorem hom_eq_of_factor_eq (A D : StarSubalgebra ℂ P)
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (Φ Ψ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a)
    (hΨ : ∀ a, G.trace (Ψ a) = G.trace a)
    (hA : ∀ a : A, Φ (a : P) = Ψ (a : P))
    (hD : ∀ d : D, Φ (d : P) = Ψ (d : P)) : Φ = Ψ := by
  have hS : factorAlgebra A D ≤ StarAlgHom.equalizer Φ Ψ := by
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · exact hA ⟨x, hx⟩
    · exact hD ⟨x, hx⟩
  have heq (x : H) : G.homIsometry Φ hΦ x = G.homIsometry Ψ hΨ x := by
    refine hgen.induction_on x
      (isClosed_eq (G.homIsometry Φ hΦ).continuous (G.homIsometry Ψ hΨ).continuous) ?_
    intro a
    change G.homIsometry Φ hΦ (G.vector (a : P)) =
      G.homIsometry Ψ hΨ (G.vector (a : P))
    rw [G.homIsometry_vector, G.homIsometry_vector]
    exact congrArg G.vector (hS a.property)
  ext a
  apply hfaithful
  simpa only [G.homIsometry_vector] using heq (G.vector a)

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D)
  (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- A choice of the published algebraic extension, with no unitary or tensor
conclusion included in that input. -/
def chosenMatrixExtension (u : Matrix.unitaryGroup α ℂ) : P →⋆ₐ[ℂ] P :=
  Classical.choose (hext u)

theorem chosenMatrixExtension_trace (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.trace (G.chosenMatrixExtension A D ι hext u a) = G.trace a :=
  (Classical.choose_spec (hext u)).1 a

theorem chosenMatrixExtension_base (u : Matrix.unitaryGroup α ℂ) (a : A) :
    G.chosenMatrixExtension A D ι hext u (a : P) = (a : P) :=
  (Classical.choose_spec (hext u)).2.1 a

theorem chosenMatrixExtension_other (u : Matrix.unitaryGroup α ℂ) (d : D) :
    G.chosenMatrixExtension A D ι hext u (d : P) =
      (matrixConjugateLetter D ι u d : P) :=
  (Classical.choose_spec (hext u)).2.2 d

include hgen hfaithful in
/-- The inverse factor conjugations give inverse ambient homomorphisms by
tracial generation; no ambient automorphism existence is assumed. -/
theorem chosenMatrixExtension_inv_comp (u : Matrix.unitaryGroup α ℂ) :
    (G.chosenMatrixExtension A D ι hext u⁻¹).comp
      (G.chosenMatrixExtension A D ι hext u) = StarAlgHom.id ℂ P := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · intro a
    exact (G.chosenMatrixExtension_trace A D ι hext u⁻¹ _).trans
      (G.chosenMatrixExtension_trace A D ι hext u a)
  · intro a
    rfl
  · intro a
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_base, StarAlgHom.coe_id, id_eq]
  · intro d
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_other,
      matrixConjugateLetter_inv, StarAlgHom.coe_id, id_eq]

/-- The actual ambient automorphism is derived from the two inverse published
factor embeddings. -/
def matrixExtensionAutomorphism (u : Matrix.unitaryGroup α ℂ) : P ≃⋆ₐ[ℂ] P :=
  StarAlgEquiv.ofStarAlgHom
    (G.chosenMatrixExtension A D ι hext u)
    (G.chosenMatrixExtension A D ι hext u⁻¹)
    (G.chosenMatrixExtension_inv_comp A D ι hgen hfaithful hext u)
    (by simpa only [inv_inv] using
      G.chosenMatrixExtension_inv_comp A D ι hgen hfaithful hext u⁻¹)

@[simp] theorem matrixExtensionAutomorphism_apply (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u a =
      G.chosenMatrixExtension A D ι hext u a := rfl

@[simp] theorem matrixExtensionAutomorphism_trace (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.trace (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u a) = G.trace a :=
  G.chosenMatrixExtension_trace A D ι hext u a

@[simp] theorem matrixExtensionAutomorphism_base (u : Matrix.unitaryGroup α ℂ) (a : A) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u (a : P) = (a : P) :=
  G.chosenMatrixExtension_base A D ι hext u a

@[simp] theorem matrixExtensionAutomorphism_other (u : Matrix.unitaryGroup α ℂ) (d : D) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u (d : P) =
      (matrixConjugateLetter D ι u d : P) :=
  G.chosenMatrixExtension_other A D ι hext u d

include hgen hfaithful in
theorem chosenMatrixExtension_one :
    G.chosenMatrixExtension A D ι hext 1 = StarAlgHom.id ℂ P := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D ι hext 1
  · intro a; rfl
  · intro a
    exact G.chosenMatrixExtension_base A D ι hext 1 a
  · intro d
    simpa only [matrixConjugateLetter_one, StarAlgHom.coe_id, id_eq] using
      G.chosenMatrixExtension_other A D ι hext 1 d

include hgen hfaithful in
theorem chosenMatrixExtension_mul (u v : Matrix.unitaryGroup α ℂ) :
    G.chosenMatrixExtension A D ι hext (u * v) =
      (G.chosenMatrixExtension A D ι hext u).comp
        (G.chosenMatrixExtension A D ι hext v) := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D ι hext (u * v)
  · intro a
    exact (G.chosenMatrixExtension_trace A D ι hext u _).trans
      (G.chosenMatrixExtension_trace A D ι hext v a)
  · intro a
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_base]
  · intro d
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_other,
      matrixConjugateLetter_mul]

/-- The ambient extensions form a genuine group action, by uniqueness on the
tracially dense generated algebra. -/
def matrixExtensionAction : Matrix.unitaryGroup α ℂ →* (P ≃⋆ₐ[ℂ] P) where
  toFun u := G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u
  map_one' := by
    apply DFunLike.ext
    intro a
    change G.chosenMatrixExtension A D ι hext 1 a = a
    exact congrArg (fun Φ : P →⋆ₐ[ℂ] P => Φ a)
      (G.chosenMatrixExtension_one A D ι hgen hfaithful hext)
  map_mul' u v := by
    apply DFunLike.ext
    intro a
    change G.chosenMatrixExtension A D ι hext (u * v) a =
      G.chosenMatrixExtension A D ι hext u (G.chosenMatrixExtension A D ι hext v a)
    exact congrArg (fun Φ : P →⋆ₐ[ℂ] P => Φ a)
      (G.chosenMatrixExtension_mul A D ι hgen hfaithful hext u v)

/-- The actual Hilbert-space unitary representation induced by the derived
free-product automorphisms. -/
def matrixExtensionUnitaryRepresentation :
    Matrix.unitaryGroup α ℂ →* unitary (H →L[ℂ] H) :=
  G.automorphismRepresentation (G.matrixExtensionAction A D ι hgen hfaithful hext)
    (fun u a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a)

@[simp] theorem matrixExtensionUnitaryRepresentation_vector
    (u : Matrix.unitaryGroup α ℂ) (a : P) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
        (G.vector a) =
      G.vector (G.chosenMatrixExtension A D ι hext u a) := by
  exact G.automorphismRepresentation_vector
    (G.matrixExtensionAction A D ι hgen hfaithful hext)
    (fun u a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a) u a

/-- The constructed matrix action fixes the whole completed base space,
by the algebraic fixation of its dense bounded vectors. -/
theorem matrixExtensionUnitaryRepresentation_base
    (u : Matrix.unitaryGroup α ℂ) (x : G.baseSpace A) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (x : H) = (x : H) := by
  exact G.automorphismUnitary_fixes_base
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a)
    A (fun a => G.matrixExtensionAutomorphism_base A D ι hgen hfaithful hext u a) x

/-- The represented ambient left action transforms under the actual
matrix-conjugation automorphism on all Hilbert vectors. -/
theorem matrixExtensionUnitaryRepresentation_left
    (u : Matrix.unitaryGroup α ℂ) (a : P) (x : H) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (G.left a x) =
    G.left (G.chosenMatrixExtension A D ι hext u a)
      ((G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H) x) := by
  exact G.automorphismUnitary_left
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a) a x

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI

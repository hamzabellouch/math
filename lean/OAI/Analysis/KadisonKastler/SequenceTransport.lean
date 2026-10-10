import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # Transport of bounded sequences and their trace quotients -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- Apply a contractive star homomorphism at every coordinate. -/
def boundedSequenceMapHom (φ : A →⋆ₐ[ℂ] B) : BoundedSequence A →⋆ₐ[ℂ] BoundedSequence B where
  toFun x := BoundedContinuousFunction.mkOfDiscrete (fun j => φ (x j)) (2 * ‖x‖) (by
    intro i j
    calc
      dist (φ (x i)) (φ (x j)) ≤ ‖φ (x i)‖ + ‖φ (x j)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖x i‖ + ‖x j‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le φ _)
        (NonUnitalStarAlgHom.norm_apply_le φ _)
      _ ≤ 2 * ‖x‖ := by linarith [x.norm_coe_le_norm i, x.norm_coe_le_norm j])
  map_one' := by ext j; exact map_one φ
  map_mul' x y := by ext j; exact map_mul φ (x j) (y j)
  map_zero' := by ext j; exact map_zero φ
  map_add' x y := by ext j; exact map_add φ (x j) (y j)
  commutes' z := by ext j; exact φ.commutes z
  map_star' x := by ext j; exact map_star φ (x j)

@[simp]
theorem boundedSequenceMapHom_apply (φ : A →⋆ₐ[ℂ] B) (x : BoundedSequence A) (j : ℕ) :
    boundedSequenceMapHom φ x j = φ (x j) := rfl

def boundedSequenceMapEquiv (e : A ≃⋆ₐ[ℂ] B) :
    BoundedSequence A ≃⋆ₐ[ℂ] BoundedSequence B :=
  StarAlgEquiv.ofBijective (boundedSequenceMapHom e.toStarAlgHom) (by
    constructor
    · intro x y h
      apply BoundedContinuousFunction.ext
      intro j
      exact e.injective (congrArg (fun z : BoundedSequence B => z j) h)
    · intro y
      refine ⟨boundedSequenceMapHom e.symm.toStarAlgHom y, ?_⟩
      apply BoundedContinuousFunction.ext
      intro j
      exact e.apply_symm_apply (y j))

namespace TraceQuotientMap

variable {τA : FaithfulTracialState A} {τB : FaithfulTracialState B}
variable {σ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

/-- A change of the concrete model for the source changes neither the
represented quotient nor its trace. -/
def comapEquiv (Q : TraceQuotientMap τB σ ω) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB.toLinearMap (e a) = τA.toLinearMap a) :
    TraceQuotientMap τA σ ω where
  quotient := Q.quotient.comp (boundedSequenceMapHom e.toStarAlgHom)
  surjective := Q.surjective.comp (boundedSequenceMapEquiv e).surjective
  trace_limit x := by
    have h := Q.trace_limit (boundedSequenceMapHom e.toStarAlgHom x)
    simpa only [boundedSequenceMapHom_apply, StarAlgEquiv.toStarAlgHom_apply, hτ,
      StarAlgHom.comp_apply] using h

@[simp]
theorem comapEquiv_quotient (Q : TraceQuotientMap τB σ ω) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB.toLinearMap (e a) = τA.toLinearMap a) (x : BoundedSequence A) :
    (Q.comapEquiv e hτ).quotient x = Q.quotient (boundedSequenceMapHom e.toStarAlgHom x) := rfl

end TraceQuotientMap

end

end KadisonKastler

end OAI

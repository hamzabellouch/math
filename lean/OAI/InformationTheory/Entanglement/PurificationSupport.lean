import OAI.InformationTheory.Entanglement.FiniteRecovery

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n : Type} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq n] in
theorem purification_finite_span (x : n → H) :
    ∃ d : ℕ, ∃ V : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] H,
      ∃ B : Matrix (Fin d) n ℂ,
        (∀ j, V (WithLp.toLp 2 (fun a => B a j))=x j) ∧
        (∀ i j, (Bᴴ*B) i j=inner ℂ (x i) (x j)) := by
  let S := Submodule.span ℂ (Set.range x)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range x)
  let b := stdOrthonormalBasis ℂ S
  let v (j : n) : S := ⟨x j,Submodule.subset_span (Set.mem_range_self j)⟩
  let V : EuclideanSpace ℂ (Fin (Module.finrank ℂ S)) →ₗᵢ[ℂ] H :=
    S.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let B : Matrix (Fin (Module.finrank ℂ S)) n ℂ := fun a j => b.repr (v j) a
  have hv (j : n) : V (WithLp.toLp 2 (fun a => B a j))=x j := by
    change ↑(b.repr.symm (b.repr (v j)))=x j
    rw [b.repr.symm_apply_apply]
  refine ⟨_,V,B,hv,?_⟩
  intro i j
  rw [← hv i,← hv j,V.inner_map_map]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Pi.star_apply,mul_comm]

theorem purification_support_recovery (i₀ : n) (x : n → H) :
    ∃ d : ℕ, ∃ V : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] H,
      ∃ B : Matrix (Fin d) n ℂ, ∃ F : Map (Fin d) n,
        CP F ∧ TracePreserving F ∧
        (∀ j, V (WithLp.toLp 2 (fun a => B a j))=x j) ∧
        (∀ A : Mat n, F (B*A*Bᴴ)=
          CFC.sqrt (Matrix.of fun i j => inner ℂ (x i) (x j))*A*CFC.sqrt (Matrix.of fun i j => inner ℂ (x i) (x j))) := by
  obtain ⟨d,V,B,hx,hgram⟩ := purification_finite_span x
  obtain ⟨F,hF,hT,hrec⟩ := finite_purification_recovery i₀ B
  have he : Bᴴ*B=Matrix.of (fun i j => inner ℂ (x i) (x j)) := by ext i j; exact hgram i j
  refine ⟨d,V,B,F,hF,hT,hx,?_⟩
  intro A
  simpa only [he] using hrec A

end SecretKey

end

end OAI

import Mathlib
import OAI.Analysis.Commutator.MatrixExpectationNested
import OAI.Analysis.Commutator.MatrixScalarApproximation
import OAI.Analysis.Commutator.MatrixTensor
import OAI.Analysis.Commutator.NormalSubalgebra
import OAI.Analysis.Commutator.RelativeMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixStageExtension

open TracialGNS MatrixExpectation

lemma expectation_map {A B I : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [Fintype I] [DecidableEq I] (f : A →⋆ₐ[ℂ] B)
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : A) :
    f (expectation φ a)=expectation (f.comp φ) (f a) := by
  rw [expectation_apply,expectation_apply]
  simp only [map_smul,map_sum,map_mul,StarAlgHom.comp_apply]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hnormal hfaith hone in
theorem exists_extension (hfac : FactorCorner.IsFactor M)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] M) (x : M) (hx : IsSelfAdjoint x)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (_ : Nonempty J)
      (θ : Matrix J J ℂ →⋆ₐ[ℂ] M),
      Function.Injective θ ∧ 2*Fintype.card I≤Fintype.card J ∧ φ.range≤θ.range ∧
      ‖algebraVector τ (expectation θ x-τ x • (1:M))‖<ε := by
  classical
  let N := RelativeMatrix.relative M φ
  have hNM : N≤M := RelativeMatrix.le_original M φ
  let inc := NormalSubalgebra.inclusion M N hNM
  let σ := NormalSubalgebra.trace M N hNM τ
  have hσ : ∀ a b : N,σ (a*b)=σ (b*a) := NormalSubalgebra.tracial M N hNM τ hτ
  have hσone : σ 1=1 := NormalSubalgebra.one M N hNM τ hone
  let y : N := ⟨(expectation φ x : H →L[ℂ] H),
    (RelativeMatrix.mem_relative M φ _).mpr ⟨(expectation φ x).property,
      fun a => congrArg Subtype.val (commutes φ x a)⟩⟩
  have hy : IsSelfAdjoint y := by
    change star y=y
    apply Subtype.ext
    exact congrArg (fun a : M => (a : H →L[ℂ] H)) (selfAdjoint φ hx).star_eq
  let o : I := Classical.choice inferInstance
  obtain ⟨J,hJ,hdec,hne,ψ,hψ,hcard,happrox⟩ :=
    MatrixApproximation.exists_scalar_expectation N σ hσ
      (NormalSubalgebra.normal M N hNM τ hnormal)
      (NormalSubalgebra.faithful M N hNM τ hfaith) hσone
      (RelativeMatrix.isFactor M φ hfac o) (RelativeMatrix.noMinimal M φ hdiffuse o) y hy hε
  let : Fintype J := hJ
  let : DecidableEq J := hdec
  let : Nonempty J := hne
  let χ := inc.comp ψ
  have hc : ∀ a b,Commute (φ a) (χ b) := by
    intro a b
    exact Subtype.ext (((RelativeMatrix.mem_relative M φ _).mp (ψ b).property).2 a)
  let θ := MatrixTensor.representation φ χ hc
  have hleft : φ.range≤θ.range := by
    rintro a ⟨b,rfl⟩
    exact MatrixTensor.left_mem φ χ hc b
  have hright : χ.range≤θ.range := by
    rintro a ⟨b,rfl⟩
    exact MatrixTensor.right_mem φ χ hc b
  have hty : σ y=τ x := trace_preserving φ τ hτ x
  have hi : inc y=expectation φ x := rfl
  have hsmall : ‖algebraVector τ (expectation χ (expectation φ x)-τ x • (1:M))‖<ε := by
    rw [NormalSubalgebra.vector_norm] at happrox
    change ‖algebraVector τ (inc (expectation ψ y-σ y • (1:N)))‖<ε at happrox
    have he : inc (expectation ψ y-σ y • (1:N))=
        expectation χ (expectation φ x)-τ x • (1:M) := by
      rw [map_sub,map_smul,map_one,expectation_map,hi,hty]
    rwa [he] at happrox
  have hcenter : algebraVector τ (expectation θ (expectation φ x)-τ x • (1:M))=
      algebraVector τ (expectation θ x-τ x • (1:M)) := by
    rw [map_sub,map_sub,nested_vector φ θ hleft τ hτ]
  have : Nontrivial M := nontrivial_of_ne (1:M) 0 (by
    intro h
    have he := congrArg τ h
    rw [hone,map_zero] at he
    exact one_ne_zero he)
  refine ⟨I×J,inferInstance,inferInstance,inferInstance,θ,
    θ.toAlgHom.toRingHom.injective,?_,hleft,?_⟩
  · rw [Fintype.card_prod]
    nlinarith [Fintype.card_pos (α:=I)]
  · rw [←hcenter]
    exact (nested_norm_le χ θ hright τ hτ (expectation φ x) (τ x)).trans_lt hsmall

end Kadison.MatrixStageExtension

end

end
end

end OAI

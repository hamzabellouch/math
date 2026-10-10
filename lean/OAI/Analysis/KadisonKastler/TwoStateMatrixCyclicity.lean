import OAI.Analysis.KadisonKastler.TwoStateMatrixRepresentation

namespace OAI

/-! # Cyclicity of the two-state matrix vector -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem twoStateMatrixRepresentation_cyclic (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (Ω : H) (ξ : K) (hM : DenseRange (algebraVectorMap M Ω))
    (hN : DenseRange (algebraVectorMap N ξ)) :
    DenseRange (fun a => twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)) := by
  let eH := (PiLp.homeomorph 2 (fun _ : Fin 2 => H)).symm
  let eK := (PiLp.homeomorph 2 (fun _ : Fin 2 => K)).symm
  let e := (WithLp.homeomorphProd 2 (FiniteHilbert (Fin 2) H)
    (FiniteHilbert (Fin 2) K)).symm
  have hdH : DenseRange (fun a : Fin 2 → Algebra M =>
      eH (fun i => algebraVectorMap M Ω (a i))) :=
    eH.surjective.denseRange.comp (DenseRange.piMap (fun _ : Fin 2 => hM)) eH.continuous
  have hdK : DenseRange (fun b : Fin 2 → Algebra N =>
      eK (fun i => algebraVectorMap N ξ (b i))) :=
    eK.surjective.denseRange.comp (DenseRange.piMap (fun _ : Fin 2 => hN)) eK.continuous
  have hd := e.surjective.denseRange.comp (hdH.prodMap hdK) e.continuous
  apply Dense.mono ?_ hd
  rintro _ ⟨⟨a, b⟩, rfl⟩
  let X : CStarMatrix (Fin 2) (Fin 2) (Algebra M) :=
    CStarMatrix.ofMatrix fun i j => if j = 0 then a i else θ.symm (b i)
  refine ⟨X, ?_⟩
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (FiniteHilbert (Fin 2) H)
    (FiniteHilbert (Fin 2) K)).injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change (twoStateMatrixRepresentation θ X (twoStateMatrixVector Ω ξ)).fst i =
      (a i).val Ω
    rw [twoStateMatrixRepresentation_vector_fst]
    rfl
  · apply PiLp.ext
    intro i
    change (twoStateMatrixRepresentation θ X (twoStateMatrixVector Ω ξ)).snd i =
      (b i).val ξ
    rw [twoStateMatrixRepresentation_vector_snd]
    change (θ (θ.symm (b i))).val ξ = (b i).val ξ
    rw [θ.apply_symm_apply]

end

end KadisonKastler

end OAI

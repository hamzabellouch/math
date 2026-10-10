import OAI.Analysis.KadisonKastler.HilbertPairRepresentation
import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # The two-state matrix representation

The first matrix column acts on the cyclic vector for the first state;
the second column acts on the cyclic vector for the second state. Their
direct sum represents the diagonal state on the two-by-two matrix algebra.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

abbrev TwoStateMatrixHilbert (H K : Type*)
    [NormedAddCommGroup H] [NormedAddCommGroup K] :=
  WithLp 2 (FiniteHilbert (Fin 2) H × FiniteHilbert (Fin 2) K)

def twoStateMatrixRepresentation (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    CStarMatrix (Fin 2) (Fin 2) (Algebra M) →⋆ₐ[ℂ]
      (TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K) :=
  hilbertPairRepresentation (matrixOperatorHom M)
    ((matrixOperatorHom N).comp (coefficientMatrixMap θ.toStarAlgHom))

def twoStateMatrixVector (Ω : H) (ξ : K) : TwoStateMatrixHilbert H K :=
  WithLp.toLp 2 (tupleSingle 0 Ω, tupleSingle 1 ξ)

omit [CompleteSpace H] [CompleteSpace K] in
theorem twoStateMatrixVector_norm_sq (Ω : H) (ξ : K) :
    ‖twoStateMatrixVector Ω ξ‖ ^ 2 = ‖Ω‖ ^ 2 + ‖ξ‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖tupleSingle (0 : Fin 2) Ω‖ ^ 2 + ‖tupleSingle (1 : Fin 2) ξ‖ ^ 2 = _
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp

theorem twoStateMatrixRepresentation_vector_fst (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (Ω : H) (ξ : K) (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) (i : Fin 2) :
    (twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)).fst i = (a i 0).val Ω := by
  change matrixOperatorHom M a (tupleSingle 0 Ω) i = _
  simp [matrixOperatorHom_apply, hilbertMatrix_apply, tupleSingle_apply,
    Fin.sum_univ_two, CStarMatrix.map_apply]

theorem twoStateMatrixRepresentation_vector_snd (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (Ω : H) (ξ : K) (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) (i : Fin 2) :
    (twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)).snd i = (θ (a i 1)).val ξ := by
  change matrixOperatorHom N (coefficientMatrixMap θ.toStarAlgHom a) (tupleSingle 1 ξ) i = _
  simp [matrixOperatorHom_apply, hilbertMatrix_apply, tupleSingle_apply,
    Fin.sum_univ_two, CStarMatrix.map_apply, coefficientMatrixMap_apply]

theorem twoStateMatrixRepresentation_separating (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (Ω : H) (ξ : K) (hM : Function.Injective (algebraVectorMap M Ω))
    (hN : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (fun a => twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)) := by
  intro a b hab
  apply CStarMatrix.ext
  intro i j
  fin_cases j
  · change a i 0 = b i 0
    apply hM
    exact (twoStateMatrixRepresentation_vector_fst θ Ω ξ a i).symm.trans
      ((congrArg (fun x : TwoStateMatrixHilbert H K => x.fst i) hab).trans
        (twoStateMatrixRepresentation_vector_fst θ Ω ξ b i))
  · change a i 1 = b i 1
    apply θ.injective
    apply hN
    exact (twoStateMatrixRepresentation_vector_snd θ Ω ξ a i).symm.trans
      ((congrArg (fun x : TwoStateMatrixHilbert H K => x.snd i) hab).trans
        (twoStateMatrixRepresentation_vector_snd θ Ω ξ b i))

end

end KadisonKastler

end OAI

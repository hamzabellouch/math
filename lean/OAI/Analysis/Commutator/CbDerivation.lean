import Mathlib
import OAI.Analysis.Commutator.CbDilation
import OAI.Analysis.Commutator.FactorMetric
import OAI.Analysis.Commutator.GramBounds
import OAI.Analysis.Commutator.TriangularCb
import OAI.Analysis.Commutator.TriangularMetric

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.CbFactor

open RectangularColumn CyclicColumns

variable {A K F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance : NormedAddCommGroup (K →L[ℂ] F) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (K →L[ℂ] F) := ContinuousLinearMap.toNormedSpace

theorem rectangular_implementation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b))
    {c : ℝ} (hc : 0≤c)
    (hcb : ∀ (ι : Type) [Fintype ι] (X : CStarMatrix ι ι A),
      ‖matrixAction (fun i j => D (X i j))‖≤c*‖X‖) :
    ∃ V : K →L[ℂ] F,‖V‖≤(1+c)^2 ∧ ∀ a : A,D a=V.comp (σ a)-(lam a).comp V := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    refine ⟨0,by simp; positivity,?_⟩
    intro a
    simp [Subsingleton.elim a 0]
  | inr hA =>
    let := hA
    let π := triangularHom σ lam D hD
    have hp : 0<1+c := by linarith
    have hπ : HasMatrixBound π.toLinearMap (1+c) := by
      intro ι _ X
      exact triangular_matrix_norm_le σ lam D hD hc (hcb ι) X
    let ρ := representation π.toLinearMap (1+c) hp hπ
    let V := leftOperator π.toLinearMap (1+c) hp hπ
    let W := rightOperator π.toLinearMap (1+c) hp hπ
    have hfactor : ∀ a : A,π a=V.adjoint.comp ((ρ a).comp W) := by
      intro a
      exact factorization π.toLinearMap (1+c) hp hπ a
    let L := leftCompression ρ V W
    have hLW : L.comp W=1 := leftCompression_right π ρ V W hfactor
    have hint : ∀ a : A,(π a).comp L=L.comp (ρ a) :=
      leftCompression_intertwines π ρ V W hfactor
    exact implementer_of_factor_metric σ lam D L W hLW
      (gram_intertwines π ρ L hint) hp.le
      (leftCompression_norm_le ρ V W (leftOperator_norm_le _ _ _ _))
      (rightOperator_norm_le _ _ _ _)

end Kadison.CbFactor

end

end
end

end OAI
